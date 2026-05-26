import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [150,160). -/

/-- Block 150 covers tail-support indices [13750,13775) and q from 22673 to 22711. -/

def TailChunk001Sub000Block150Part000SupportExplicit : Finset ℕ :=
  ([22673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part000 : ℚ :=
  (16504074851 : ℚ) / 6141581680449945600

def SurrogateDiagonalTailChunk001Sub000Block150Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22673
    = surrogateDiagTailX0RatChunk001Sub000Block150Part000

theorem surrogateDiagonalTailChunk001Sub000Block150Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part000] using hcert

def TailChunk001Sub000Block150Part001SupportExplicit : Finset ℕ :=
  ([22674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part001 : ℚ :=
  (446352671525 : ℚ) / 4075347629437698624

def SurrogateDiagonalTailChunk001Sub000Block150Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22674
    = surrogateDiagTailX0RatChunk001Sub000Block150Part001

theorem surrogateDiagonalTailChunk001Sub000Block150Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part001] using hcert

def TailChunk001Sub000Block150Part002SupportExplicit : Finset ℕ :=
  ([22677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part002 : ℚ :=
  (125025 : ℚ) / 26104629717411968

def SurrogateDiagonalTailChunk001Sub000Block150Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22677
    = surrogateDiagTailX0RatChunk001Sub000Block150Part002

theorem surrogateDiagonalTailChunk001Sub000Block150Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part002] using hcert

def TailChunk001Sub000Block150Part003SupportExplicit : Finset ℕ :=
  ([22678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part003 : ℚ :=
  (72274788825 : ℚ) / 3932587439641591808

def SurrogateDiagonalTailChunk001Sub000Block150Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22678
    = surrogateDiagTailX0RatChunk001Sub000Block150Part003

theorem surrogateDiagonalTailChunk001Sub000Block150Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part003] using hcert

def TailChunk001Sub000Block150Part004SupportExplicit : Finset ℕ :=
  ([22679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22679
    = surrogateDiagTailX0RatChunk001Sub000Block150Part004

theorem surrogateDiagonalTailChunk001Sub000Block150Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part004] using hcert

def TailChunk001Sub000Block150Part005SupportExplicit : Finset ℕ :=
  ([22681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part005 : ℚ :=
  (198250447075 : ℚ) / 589172612411871756288

def SurrogateDiagonalTailChunk001Sub000Block150Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22681
    = surrogateDiagTailX0RatChunk001Sub000Block150Part005

theorem surrogateDiagonalTailChunk001Sub000Block150Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part005] using hcert

def TailChunk001Sub000Block150Part006SupportExplicit : Finset ℕ :=
  ([22682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part006 : ℚ :=
  (1337572213 : ℚ) / 112573391176200000

def SurrogateDiagonalTailChunk001Sub000Block150Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22682
    = surrogateDiagTailX0RatChunk001Sub000Block150Part006

theorem surrogateDiagonalTailChunk001Sub000Block150Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part006] using hcert

def TailChunk001Sub000Block150Part007SupportExplicit : Finset ℕ :=
  ([22683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part007 : ℚ :=
  (1667 : ℚ) / 348430292582400

def SurrogateDiagonalTailChunk001Sub000Block150Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22683
    = surrogateDiagTailX0RatChunk001Sub000Block150Part007

theorem surrogateDiagonalTailChunk001Sub000Block150Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part007] using hcert

def TailChunk001Sub000Block150Part008SupportExplicit : Finset ℕ :=
  ([22685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part008 : ℚ :=
  (53239689275 : ℚ) / 6712909407014879232

def SurrogateDiagonalTailChunk001Sub000Block150Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22685
    = surrogateDiagTailX0RatChunk001Sub000Block150Part008

theorem surrogateDiagonalTailChunk001Sub000Block150Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part008] using hcert

def TailChunk001Sub000Block150Part009SupportExplicit : Finset ℕ :=
  ([22686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part009 : ℚ :=
  (922756144225 : ℚ) / 6455020457670985728

def SurrogateDiagonalTailChunk001Sub000Block150Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22686
    = surrogateDiagTailX0RatChunk001Sub000Block150Part009

theorem surrogateDiagonalTailChunk001Sub000Block150Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part009] using hcert

def TailChunk001Sub000Block150Part010SupportExplicit : Finset ℕ :=
  ([22690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part010 : ℚ :=
  (214699949575 : ℚ) / 5645699653982846976

def SurrogateDiagonalTailChunk001Sub000Block150Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22690
    = surrogateDiagTailX0RatChunk001Sub000Block150Part010

theorem surrogateDiagonalTailChunk001Sub000Block150Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part010] using hcert

def TailChunk001Sub000Block150Part011SupportExplicit : Finset ℕ :=
  ([22691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22691
    = surrogateDiagTailX0RatChunk001Sub000Block150Part011

theorem surrogateDiagonalTailChunk001Sub000Block150Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part011] using hcert

def TailChunk001Sub000Block150Part012SupportExplicit : Finset ℕ :=
  ([22693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part012 : ℚ :=
  (1336254901 : ℚ) / 1130112064738504200

def SurrogateDiagonalTailChunk001Sub000Block150Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22693
    = surrogateDiagTailX0RatChunk001Sub000Block150Part012

theorem surrogateDiagonalTailChunk001Sub000Block150Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part012] using hcert

def TailChunk001Sub000Block150Part013SupportExplicit : Finset ℕ :=
  ([22694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part013 : ℚ :=
  (365742811 : ℚ) / 16533246852172800

def SurrogateDiagonalTailChunk001Sub000Block150Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22694
    = surrogateDiagTailX0RatChunk001Sub000Block150Part013

theorem surrogateDiagonalTailChunk001Sub000Block150Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part013] using hcert

def TailChunk001Sub000Block150Part014SupportExplicit : Finset ℕ :=
  ([22695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part014 : ℚ :=
  (83589035775 : ℚ) / 3354410277545181184

def SurrogateDiagonalTailChunk001Sub000Block150Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22695
    = surrogateDiagTailX0RatChunk001Sub000Block150Part014

theorem surrogateDiagonalTailChunk001Sub000Block150Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part014] using hcert

def TailChunk001Sub000Block150Part015SupportExplicit : Finset ℕ :=
  ([22697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22697
    = surrogateDiagTailX0RatChunk001Sub000Block150Part015

theorem surrogateDiagonalTailChunk001Sub000Block150Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part015] using hcert

def TailChunk001Sub000Block150Part016SupportExplicit : Finset ℕ :=
  ([22699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22699
    = surrogateDiagTailX0RatChunk001Sub000Block150Part016

theorem surrogateDiagonalTailChunk001Sub000Block150Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part016] using hcert

def TailChunk001Sub000Block150Part017SupportExplicit : Finset ℕ :=
  ([22701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part017 : ℚ :=
  (14052214975 : ℚ) / 1007117478645645312

def SurrogateDiagonalTailChunk001Sub000Block150Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22701
    = surrogateDiagTailX0RatChunk001Sub000Block150Part017

theorem surrogateDiagonalTailChunk001Sub000Block150Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part017] using hcert

def TailChunk001Sub000Block150Part018SupportExplicit : Finset ℕ :=
  ([22702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22702
    = surrogateDiagTailX0RatChunk001Sub000Block150Part018

theorem surrogateDiagonalTailChunk001Sub000Block150Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part018] using hcert

def TailChunk001Sub000Block150Part019SupportExplicit : Finset ℕ :=
  ([22703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part019 : ℚ :=
  (2363161577 : ℚ) / 12411767040524697600

def SurrogateDiagonalTailChunk001Sub000Block150Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22703
    = surrogateDiagTailX0RatChunk001Sub000Block150Part019

theorem surrogateDiagonalTailChunk001Sub000Block150Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part019] using hcert

def TailChunk001Sub000Block150Part020SupportExplicit : Finset ℕ :=
  ([22705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part020 : ℚ :=
  (1449041045425 : ℚ) / 215607901600503595008

def SurrogateDiagonalTailChunk001Sub000Block150Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22705
    = surrogateDiagTailX0RatChunk001Sub000Block150Part020

theorem surrogateDiagonalTailChunk001Sub000Block150Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part020] using hcert

def TailChunk001Sub000Block150Part021SupportExplicit : Finset ℕ :=
  ([22706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22706
    = surrogateDiagTailX0RatChunk001Sub000Block150Part021

theorem surrogateDiagonalTailChunk001Sub000Block150Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part021] using hcert

def TailChunk001Sub000Block150Part022SupportExplicit : Finset ℕ :=
  ([22709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block150Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22709
    = surrogateDiagTailX0RatChunk001Sub000Block150Part022

theorem surrogateDiagonalTailChunk001Sub000Block150Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part022] using hcert

def TailChunk001Sub000Block150Part023SupportExplicit : Finset ℕ :=
  ([22710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part023 : ℚ :=
  (334257686075 : ℚ) / 1115199931650932736

def SurrogateDiagonalTailChunk001Sub000Block150Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22710
    = surrogateDiagTailX0RatChunk001Sub000Block150Part023

theorem surrogateDiagonalTailChunk001Sub000Block150Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part023] using hcert

def TailChunk001Sub000Block150Part024SupportExplicit : Finset ℕ :=
  ([22711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block150Part024 : ℚ :=
  (35945078575 : ℚ) / 30116799514781301888

def SurrogateDiagonalTailChunk001Sub000Block150Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22711
    = surrogateDiagTailX0RatChunk001Sub000Block150Part024

theorem surrogateDiagonalTailChunk001Sub000Block150Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block150Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block150Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block150Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block150Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block150Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block150Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block150HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block150Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block150Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block150Part000
    + surrogateDiagTailX0RatChunk001Sub000Block150Part001
    + surrogateDiagTailX0RatChunk001Sub000Block150Part002
    + surrogateDiagTailX0RatChunk001Sub000Block150Part003
    + surrogateDiagTailX0RatChunk001Sub000Block150Part004
    + surrogateDiagTailX0RatChunk001Sub000Block150Part005
    + surrogateDiagTailX0RatChunk001Sub000Block150Part006
    + surrogateDiagTailX0RatChunk001Sub000Block150Part007
    + surrogateDiagTailX0RatChunk001Sub000Block150Part008
    + surrogateDiagTailX0RatChunk001Sub000Block150Part009

def surrogateDiagonalTailChunk001Sub000Block150MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block150Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block150Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block150Part010
    + surrogateDiagTailX0RatChunk001Sub000Block150Part011
    + surrogateDiagTailX0RatChunk001Sub000Block150Part012
    + surrogateDiagTailX0RatChunk001Sub000Block150Part013
    + surrogateDiagTailX0RatChunk001Sub000Block150Part014
    + surrogateDiagTailX0RatChunk001Sub000Block150Part015
    + surrogateDiagTailX0RatChunk001Sub000Block150Part016
    + surrogateDiagTailX0RatChunk001Sub000Block150Part017
    + surrogateDiagTailX0RatChunk001Sub000Block150Part018
    + surrogateDiagTailX0RatChunk001Sub000Block150Part019

def surrogateDiagonalTailChunk001Sub000Block150TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block150Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block150Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block150Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block150Part020
    + surrogateDiagTailX0RatChunk001Sub000Block150Part021
    + surrogateDiagTailX0RatChunk001Sub000Block150Part022
    + surrogateDiagTailX0RatChunk001Sub000Block150Part023
    + surrogateDiagTailX0RatChunk001Sub000Block150Part024

def surrogateDiagonalTailChunk001Sub000Block150Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block150HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block150MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block150TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block150 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block150Part000
    + surrogateDiagTailX0RatChunk001Sub000Block150Part001
    + surrogateDiagTailX0RatChunk001Sub000Block150Part002
    + surrogateDiagTailX0RatChunk001Sub000Block150Part003
    + surrogateDiagTailX0RatChunk001Sub000Block150Part004
    + surrogateDiagTailX0RatChunk001Sub000Block150Part005
    + surrogateDiagTailX0RatChunk001Sub000Block150Part006
    + surrogateDiagTailX0RatChunk001Sub000Block150Part007
    + surrogateDiagTailX0RatChunk001Sub000Block150Part008
    + surrogateDiagTailX0RatChunk001Sub000Block150Part009
    + surrogateDiagTailX0RatChunk001Sub000Block150Part010
    + surrogateDiagTailX0RatChunk001Sub000Block150Part011
    + surrogateDiagTailX0RatChunk001Sub000Block150Part012
    + surrogateDiagTailX0RatChunk001Sub000Block150Part013
    + surrogateDiagTailX0RatChunk001Sub000Block150Part014
    + surrogateDiagTailX0RatChunk001Sub000Block150Part015
    + surrogateDiagTailX0RatChunk001Sub000Block150Part016
    + surrogateDiagTailX0RatChunk001Sub000Block150Part017
    + surrogateDiagTailX0RatChunk001Sub000Block150Part018
    + surrogateDiagTailX0RatChunk001Sub000Block150Part019
    + surrogateDiagTailX0RatChunk001Sub000Block150Part020
    + surrogateDiagTailX0RatChunk001Sub000Block150Part021
    + surrogateDiagTailX0RatChunk001Sub000Block150Part022
    + surrogateDiagTailX0RatChunk001Sub000Block150Part023
    + surrogateDiagTailX0RatChunk001Sub000Block150Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block150_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block150Head + surrogateDiagTailX0RatChunk001Sub000Block150Mid + surrogateDiagTailX0RatChunk001Sub000Block150Tail =
      surrogateDiagTailX0RatChunk001Sub000Block150 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block150Head surrogateDiagTailX0RatChunk001Sub000Block150Mid surrogateDiagTailX0RatChunk001Sub000Block150Tail surrogateDiagTailX0RatChunk001Sub000Block150
  ring

def SurrogateDiagonalTailChunk001Sub000Block150HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block150HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block150Head

def SurrogateDiagonalTailChunk001Sub000Block150MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block150MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block150Mid

def SurrogateDiagonalTailChunk001Sub000Block150TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block150TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block150Tail

theorem surrogateDiagonalTailChunk001Sub000Block150_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block150HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block150MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block150TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block150Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block150 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block150HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block150MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block150TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block150Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block150_eq_head_add_mid_add_tail

/-- Block 151 covers tail-support indices [13775,13800) and q from 22713 to 22751. -/

def TailChunk001Sub000Block151Part000SupportExplicit : Finset ℕ :=
  ([22713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part000 : ℚ :=
  (7467175 : ℚ) / 7961897185837056

def SurrogateDiagonalTailChunk001Sub000Block151Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22713
    = surrogateDiagTailX0RatChunk001Sub000Block151Part000

theorem surrogateDiagonalTailChunk001Sub000Block151Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part000] using hcert

def TailChunk001Sub000Block151Part001SupportExplicit : Finset ℕ :=
  ([22714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part001 : ℚ :=
  (391642303 : ℚ) / 148580954434437120

def SurrogateDiagonalTailChunk001Sub000Block151Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22714
    = surrogateDiagTailX0RatChunk001Sub000Block151Part001

theorem surrogateDiagonalTailChunk001Sub000Block151Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part001] using hcert

def TailChunk001Sub000Block151Part002SupportExplicit : Finset ℕ :=
  ([22715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part002 : ℚ :=
  (461861671 : ℚ) / 26078421425356800

def SurrogateDiagonalTailChunk001Sub000Block151Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22715
    = surrogateDiagTailX0RatChunk001Sub000Block151Part002

theorem surrogateDiagonalTailChunk001Sub000Block151Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part002] using hcert

def TailChunk001Sub000Block151Part003SupportExplicit : Finset ℕ :=
  ([22717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block151Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22717
    = surrogateDiagTailX0RatChunk001Sub000Block151Part003

theorem surrogateDiagonalTailChunk001Sub000Block151Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part003] using hcert

def TailChunk001Sub000Block151Part004SupportExplicit : Finset ℕ :=
  ([22718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part004 : ℚ :=
  (104594239375 : ℚ) / 36823288275741984768

def SurrogateDiagonalTailChunk001Sub000Block151Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22718
    = surrogateDiagTailX0RatChunk001Sub000Block151Part004

theorem surrogateDiagonalTailChunk001Sub000Block151Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part004] using hcert

def TailChunk001Sub000Block151Part005SupportExplicit : Finset ℕ :=
  ([22719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part005 : ℚ :=
  (41675 : ℚ) / 8766195531503616

def SurrogateDiagonalTailChunk001Sub000Block151Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22719
    = surrogateDiagTailX0RatChunk001Sub000Block151Part005

theorem surrogateDiagonalTailChunk001Sub000Block151Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part005] using hcert

def TailChunk001Sub000Block151Part006SupportExplicit : Finset ℕ :=
  ([22721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block151Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22721
    = surrogateDiagTailX0RatChunk001Sub000Block151Part006

theorem surrogateDiagonalTailChunk001Sub000Block151Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part006] using hcert

def TailChunk001Sub000Block151Part007SupportExplicit : Finset ℕ :=
  ([22722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part007 : ℚ :=
  (1939370459 : ℚ) / 8817731654492160

def SurrogateDiagonalTailChunk001Sub000Block151Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22722
    = surrogateDiagTailX0RatChunk001Sub000Block151Part007

theorem surrogateDiagonalTailChunk001Sub000Block151Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part007] using hcert

def TailChunk001Sub000Block151Part008SupportExplicit : Finset ℕ :=
  ([22723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part008 : ℚ :=
  (8403750067 : ℚ) / 23260347216271411200

def SurrogateDiagonalTailChunk001Sub000Block151Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22723
    = surrogateDiagTailX0RatChunk001Sub000Block151Part008

theorem surrogateDiagonalTailChunk001Sub000Block151Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part008] using hcert

def TailChunk001Sub000Block151Part009SupportExplicit : Finset ℕ :=
  ([22726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part009 : ℚ :=
  (10768946821 : ℚ) / 1134502975800115200

def SurrogateDiagonalTailChunk001Sub000Block151Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22726
    = surrogateDiagTailX0RatChunk001Sub000Block151Part009

theorem surrogateDiagonalTailChunk001Sub000Block151Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part009] using hcert

def TailChunk001Sub000Block151Part010SupportExplicit : Finset ℕ :=
  ([22727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block151Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22727
    = surrogateDiagTailX0RatChunk001Sub000Block151Part010

theorem surrogateDiagonalTailChunk001Sub000Block151Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part010] using hcert

def TailChunk001Sub000Block151Part011SupportExplicit : Finset ℕ :=
  ([22729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part011 : ℚ :=
  (173542739381 : ℚ) / 2214196611687383040

def SurrogateDiagonalTailChunk001Sub000Block151Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22729
    = surrogateDiagTailX0RatChunk001Sub000Block151Part011

theorem surrogateDiagonalTailChunk001Sub000Block151Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part011] using hcert

def TailChunk001Sub000Block151Part012SupportExplicit : Finset ℕ :=
  ([22730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part012 : ℚ :=
  (1936461899775 : ℚ) / 5685633713497440256

def SurrogateDiagonalTailChunk001Sub000Block151Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22730
    = surrogateDiagTailX0RatChunk001Sub000Block151Part012

theorem surrogateDiagonalTailChunk001Sub000Block151Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part012] using hcert

def TailChunk001Sub000Block151Part013SupportExplicit : Finset ℕ :=
  ([22731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part013 : ℚ :=
  (14349568242325 : ℚ) / 131797358306508177408

def SurrogateDiagonalTailChunk001Sub000Block151Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22731
    = surrogateDiagTailX0RatChunk001Sub000Block151Part013

theorem surrogateDiagonalTailChunk001Sub000Block151Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part013] using hcert

def TailChunk001Sub000Block151Part014SupportExplicit : Finset ℕ :=
  ([22733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part014 : ℚ :=
  (3503587661825 : ℚ) / 70298577830450212992

def SurrogateDiagonalTailChunk001Sub000Block151Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22733
    = surrogateDiagTailX0RatChunk001Sub000Block151Part014

theorem surrogateDiagonalTailChunk001Sub000Block151Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part014] using hcert

def TailChunk001Sub000Block151Part015SupportExplicit : Finset ℕ :=
  ([22735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part015 : ℚ :=
  (21961065390025 : ℚ) / 273391211645159098368

def SurrogateDiagonalTailChunk001Sub000Block151Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22735
    = surrogateDiagTailX0RatChunk001Sub000Block151Part015

theorem surrogateDiagonalTailChunk001Sub000Block151Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part015] using hcert

def TailChunk001Sub000Block151Part016SupportExplicit : Finset ℕ :=
  ([22737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part016 : ℚ :=
  (996357929 : ℚ) / 5832461234995200

def SurrogateDiagonalTailChunk001Sub000Block151Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22737
    = surrogateDiagTailX0RatChunk001Sub000Block151Part016

theorem surrogateDiagonalTailChunk001Sub000Block151Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part016] using hcert

def TailChunk001Sub000Block151Part017SupportExplicit : Finset ℕ :=
  ([22738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part017 : ℚ :=
  (2019596265625 : ℚ) / 10440063188285993472

def SurrogateDiagonalTailChunk001Sub000Block151Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22738
    = surrogateDiagTailX0RatChunk001Sub000Block151Part017

theorem surrogateDiagonalTailChunk001Sub000Block151Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part017] using hcert

def TailChunk001Sub000Block151Part018SupportExplicit : Finset ℕ :=
  ([22739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part018 : ℚ :=
  (8079095640625 : ℚ) / 167099794634410837842

def SurrogateDiagonalTailChunk001Sub000Block151Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22739
    = surrogateDiagTailX0RatChunk001Sub000Block151Part018

theorem surrogateDiagonalTailChunk001Sub000Block151Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part018] using hcert

def TailChunk001Sub000Block151Part019SupportExplicit : Finset ℕ :=
  ([22741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part019 : ℚ :=
  (12928827025 : ℚ) / 267453750031755552

def SurrogateDiagonalTailChunk001Sub000Block151Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22741
    = surrogateDiagTailX0RatChunk001Sub000Block151Part019

theorem surrogateDiagonalTailChunk001Sub000Block151Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part019] using hcert

def TailChunk001Sub000Block151Part020SupportExplicit : Finset ℕ :=
  ([22742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part020 : ℚ :=
  (95618652325 : ℚ) / 471654572946898944

def SurrogateDiagonalTailChunk001Sub000Block151Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22742
    = surrogateDiagTailX0RatChunk001Sub000Block151Part020

theorem surrogateDiagonalTailChunk001Sub000Block151Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part020] using hcert

def TailChunk001Sub000Block151Part021SupportExplicit : Finset ℕ :=
  ([22745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part021 : ℚ :=
  (21980391958975 : ℚ) / 273872640032517685248

def SurrogateDiagonalTailChunk001Sub000Block151Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22745
    = surrogateDiagTailX0RatChunk001Sub000Block151Part021

theorem surrogateDiagonalTailChunk001Sub000Block151Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part021] using hcert

def TailChunk001Sub000Block151Part022SupportExplicit : Finset ℕ :=
  ([22746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part022 : ℚ :=
  (678382672375 : ℚ) / 1061420373783871488

def SurrogateDiagonalTailChunk001Sub000Block151Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22746
    = surrogateDiagTailX0RatChunk001Sub000Block151Part022

theorem surrogateDiagonalTailChunk001Sub000Block151Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part022] using hcert

def TailChunk001Sub000Block151Part023SupportExplicit : Finset ℕ :=
  ([22749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part023 : ℚ :=
  (14372305241725 : ℚ) / 132215375237577057408

def SurrogateDiagonalTailChunk001Sub000Block151Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22749
    = surrogateDiagTailX0RatChunk001Sub000Block151Part023

theorem surrogateDiagonalTailChunk001Sub000Block151Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part023] using hcert

def TailChunk001Sub000Block151Part024SupportExplicit : Finset ℕ :=
  ([22751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block151Part024 : ℚ :=
  (517608001 : ℚ) / 10716980623781250

def SurrogateDiagonalTailChunk001Sub000Block151Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22751
    = surrogateDiagTailX0RatChunk001Sub000Block151Part024

theorem surrogateDiagonalTailChunk001Sub000Block151Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block151Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block151Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block151Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block151Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block151Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block151Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block151HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block151Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block151Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block151Part000
    + surrogateDiagTailX0RatChunk001Sub000Block151Part001
    + surrogateDiagTailX0RatChunk001Sub000Block151Part002
    + surrogateDiagTailX0RatChunk001Sub000Block151Part003
    + surrogateDiagTailX0RatChunk001Sub000Block151Part004
    + surrogateDiagTailX0RatChunk001Sub000Block151Part005
    + surrogateDiagTailX0RatChunk001Sub000Block151Part006
    + surrogateDiagTailX0RatChunk001Sub000Block151Part007
    + surrogateDiagTailX0RatChunk001Sub000Block151Part008
    + surrogateDiagTailX0RatChunk001Sub000Block151Part009

def surrogateDiagonalTailChunk001Sub000Block151MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block151Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block151Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block151Part010
    + surrogateDiagTailX0RatChunk001Sub000Block151Part011
    + surrogateDiagTailX0RatChunk001Sub000Block151Part012
    + surrogateDiagTailX0RatChunk001Sub000Block151Part013
    + surrogateDiagTailX0RatChunk001Sub000Block151Part014
    + surrogateDiagTailX0RatChunk001Sub000Block151Part015
    + surrogateDiagTailX0RatChunk001Sub000Block151Part016
    + surrogateDiagTailX0RatChunk001Sub000Block151Part017
    + surrogateDiagTailX0RatChunk001Sub000Block151Part018
    + surrogateDiagTailX0RatChunk001Sub000Block151Part019

def surrogateDiagonalTailChunk001Sub000Block151TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block151Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block151Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block151Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block151Part020
    + surrogateDiagTailX0RatChunk001Sub000Block151Part021
    + surrogateDiagTailX0RatChunk001Sub000Block151Part022
    + surrogateDiagTailX0RatChunk001Sub000Block151Part023
    + surrogateDiagTailX0RatChunk001Sub000Block151Part024

def surrogateDiagonalTailChunk001Sub000Block151Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block151HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block151MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block151TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block151 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block151Part000
    + surrogateDiagTailX0RatChunk001Sub000Block151Part001
    + surrogateDiagTailX0RatChunk001Sub000Block151Part002
    + surrogateDiagTailX0RatChunk001Sub000Block151Part003
    + surrogateDiagTailX0RatChunk001Sub000Block151Part004
    + surrogateDiagTailX0RatChunk001Sub000Block151Part005
    + surrogateDiagTailX0RatChunk001Sub000Block151Part006
    + surrogateDiagTailX0RatChunk001Sub000Block151Part007
    + surrogateDiagTailX0RatChunk001Sub000Block151Part008
    + surrogateDiagTailX0RatChunk001Sub000Block151Part009
    + surrogateDiagTailX0RatChunk001Sub000Block151Part010
    + surrogateDiagTailX0RatChunk001Sub000Block151Part011
    + surrogateDiagTailX0RatChunk001Sub000Block151Part012
    + surrogateDiagTailX0RatChunk001Sub000Block151Part013
    + surrogateDiagTailX0RatChunk001Sub000Block151Part014
    + surrogateDiagTailX0RatChunk001Sub000Block151Part015
    + surrogateDiagTailX0RatChunk001Sub000Block151Part016
    + surrogateDiagTailX0RatChunk001Sub000Block151Part017
    + surrogateDiagTailX0RatChunk001Sub000Block151Part018
    + surrogateDiagTailX0RatChunk001Sub000Block151Part019
    + surrogateDiagTailX0RatChunk001Sub000Block151Part020
    + surrogateDiagTailX0RatChunk001Sub000Block151Part021
    + surrogateDiagTailX0RatChunk001Sub000Block151Part022
    + surrogateDiagTailX0RatChunk001Sub000Block151Part023
    + surrogateDiagTailX0RatChunk001Sub000Block151Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block151_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block151Head + surrogateDiagTailX0RatChunk001Sub000Block151Mid + surrogateDiagTailX0RatChunk001Sub000Block151Tail =
      surrogateDiagTailX0RatChunk001Sub000Block151 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block151Head surrogateDiagTailX0RatChunk001Sub000Block151Mid surrogateDiagTailX0RatChunk001Sub000Block151Tail surrogateDiagTailX0RatChunk001Sub000Block151
  ring

def SurrogateDiagonalTailChunk001Sub000Block151HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block151HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block151Head

def SurrogateDiagonalTailChunk001Sub000Block151MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block151MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block151Mid

def SurrogateDiagonalTailChunk001Sub000Block151TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block151TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block151Tail

theorem surrogateDiagonalTailChunk001Sub000Block151_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block151HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block151MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block151TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block151Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block151 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block151HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block151MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block151TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block151Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block151_eq_head_add_mid_add_tail

/-- Block 152 covers tail-support indices [13800,13825) and q from 22753 to 22791. -/

def TailChunk001Sub000Block152Part000SupportExplicit : Finset ℕ :=
  ([22753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part000 : ℚ :=
  (1250438598553 : ℚ) / 24823534081049395200

def SurrogateDiagonalTailChunk001Sub000Block152Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22753
    = surrogateDiagTailX0RatChunk001Sub000Block152Part000

theorem surrogateDiagonalTailChunk001Sub000Block152Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part000] using hcert

def TailChunk001Sub000Block152Part001SupportExplicit : Finset ℕ :=
  ([22754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part001 : ℚ :=
  (34018704203 : ℚ) / 161530189001884800

def SurrogateDiagonalTailChunk001Sub000Block152Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22754
    = surrogateDiagTailX0RatChunk001Sub000Block152Part001

theorem surrogateDiagonalTailChunk001Sub000Block152Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part001] using hcert

def TailChunk001Sub000Block152Part002SupportExplicit : Finset ℕ :=
  ([22755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part002 : ℚ :=
  (38784952627 : ℚ) / 195728585313484800

def SurrogateDiagonalTailChunk001Sub000Block152Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22755
    = surrogateDiagTailX0RatChunk001Sub000Block152Part002

theorem surrogateDiagonalTailChunk001Sub000Block152Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part002] using hcert

def TailChunk001Sub000Block152Part003SupportExplicit : Finset ℕ :=
  ([22757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part003 : ℚ :=
  (195433878989 : ℚ) / 2892379610250000000

def SurrogateDiagonalTailChunk001Sub000Block152Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22757
    = surrogateDiagTailX0RatChunk001Sub000Block152Part003

theorem surrogateDiagonalTailChunk001Sub000Block152Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part003] using hcert

def TailChunk001Sub000Block152Part004SupportExplicit : Finset ℕ :=
  ([22758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part004 : ℚ :=
  (2247431902925 : ℚ) / 4136091716566646784

def SurrogateDiagonalTailChunk001Sub000Block152Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22758
    = surrogateDiagTailX0RatChunk001Sub000Block152Part004

theorem surrogateDiagonalTailChunk001Sub000Block152Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part004] using hcert

def TailChunk001Sub000Block152Part005SupportExplicit : Finset ℕ :=
  ([22759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part005 : ℚ :=
  (90895432887 : ℚ) / 1524430894995289600

def SurrogateDiagonalTailChunk001Sub000Block152Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22759
    = surrogateDiagTailX0RatChunk001Sub000Block152Part005

theorem surrogateDiagonalTailChunk001Sub000Block152Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part005] using hcert

def TailChunk001Sub000Block152Part006SupportExplicit : Finset ℕ :=
  ([22762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part006 : ℚ :=
  (2475640067125 : ℚ) / 11189234108325476736

def SurrogateDiagonalTailChunk001Sub000Block152Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22762
    = surrogateDiagTailX0RatChunk001Sub000Block152Part006

theorem surrogateDiagonalTailChunk001Sub000Block152Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part006] using hcert

def TailChunk001Sub000Block152Part007SupportExplicit : Finset ℕ :=
  ([22763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part007 : ℚ :=
  (24671768799775 : ℚ) / 367817561414270189568

def SurrogateDiagonalTailChunk001Sub000Block152Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22763
    = surrogateDiagTailX0RatChunk001Sub000Block152Part007

theorem surrogateDiagonalTailChunk001Sub000Block152Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part007] using hcert

def TailChunk001Sub000Block152Part008SupportExplicit : Finset ℕ :=
  ([22765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part008 : ℚ :=
  (1378371245525 : ℚ) / 16644444573979901952

def SurrogateDiagonalTailChunk001Sub000Block152Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22765
    = surrogateDiagTailX0RatChunk001Sub000Block152Part008

theorem surrogateDiagonalTailChunk001Sub000Block152Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part008] using hcert

def TailChunk001Sub000Block152Part009SupportExplicit : Finset ℕ :=
  ([22766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part009 : ℚ :=
  (2024573265625 : ℚ) / 10491587153104660722

def SurrogateDiagonalTailChunk001Sub000Block152Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22766
    = surrogateDiagTailX0RatChunk001Sub000Block152Part009

theorem surrogateDiagonalTailChunk001Sub000Block152Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part009] using hcert

def TailChunk001Sub000Block152Part010SupportExplicit : Finset ℕ :=
  ([22767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part010 : ℚ :=
  (14395060241125 : ℚ) / 132634385738014476288

def SurrogateDiagonalTailChunk001Sub000Block152Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22767
    = surrogateDiagTailX0RatChunk001Sub000Block152Part010

theorem surrogateDiagonalTailChunk001Sub000Block152Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part010] using hcert

def TailChunk001Sub000Block152Part011SupportExplicit : Finset ℕ :=
  ([22769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part011 : ℚ :=
  (8100427515625 : ℚ) / 167983412122911055872

def SurrogateDiagonalTailChunk001Sub000Block152Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22769
    = surrogateDiagTailX0RatChunk001Sub000Block152Part011

theorem surrogateDiagonalTailChunk001Sub000Block152Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part011] using hcert

def TailChunk001Sub000Block152Part012SupportExplicit : Finset ℕ :=
  ([22771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part012 : ℚ :=
  (24459308572225 : ℚ) / 362438236079597242368

def SurrogateDiagonalTailChunk001Sub000Block152Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22771
    = surrogateDiagTailX0RatChunk001Sub000Block152Part012

theorem surrogateDiagonalTailChunk001Sub000Block152Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part012] using hcert

def TailChunk001Sub000Block152Part013SupportExplicit : Finset ℕ :=
  ([22773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part013 : ℚ :=
  (52373269967 : ℚ) / 482815552617763200

def SurrogateDiagonalTailChunk001Sub000Block152Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22773
    = surrogateDiagTailX0RatChunk001Sub000Block152Part013

theorem surrogateDiagonalTailChunk001Sub000Block152Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part013] using hcert

def TailChunk001Sub000Block152Part014SupportExplicit : Finset ℕ :=
  ([22774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part014 : ℚ :=
  (269906314025 : ℚ) / 1326006796447383552

def SurrogateDiagonalTailChunk001Sub000Block152Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22774
    = surrogateDiagTailX0RatChunk001Sub000Block152Part014

theorem surrogateDiagonalTailChunk001Sub000Block152Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part014] using hcert

def TailChunk001Sub000Block152Part015SupportExplicit : Finset ℕ :=
  ([22777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part015 : ℚ :=
  (8106120765625 : ℚ) / 168219634146028687872

def SurrogateDiagonalTailChunk001Sub000Block152Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22777
    = surrogateDiagTailX0RatChunk001Sub000Block152Part015

theorem surrogateDiagonalTailChunk001Sub000Block152Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part015] using hcert

def TailChunk001Sub000Block152Part016SupportExplicit : Finset ℕ :=
  ([22778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part016 : ℚ :=
  (98153185375 : ℚ) / 353943589921481682

def SurrogateDiagonalTailChunk001Sub000Block152Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22778
    = surrogateDiagTailX0RatChunk001Sub000Block152Part016

theorem surrogateDiagonalTailChunk001Sub000Block152Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part016] using hcert

def TailChunk001Sub000Block152Part017SupportExplicit : Finset ℕ :=
  ([22781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part017 : ℚ :=
  (966364604287 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub000Block152Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22781
    = surrogateDiagTailX0RatChunk001Sub000Block152Part017

theorem surrogateDiagonalTailChunk001Sub000Block152Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part017] using hcert

def TailChunk001Sub000Block152Part018SupportExplicit : Finset ℕ :=
  ([22782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part018 : ℚ :=
  (3603028620325 : ℚ) / 8307142426964379648

def SurrogateDiagonalTailChunk001Sub000Block152Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22782
    = surrogateDiagTailX0RatChunk001Sub000Block152Part018

theorem surrogateDiagonalTailChunk001Sub000Block152Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part018] using hcert

def TailChunk001Sub000Block152Part019SupportExplicit : Finset ℕ :=
  ([22783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part019 : ℚ :=
  (8110392015625 : ℚ) / 168396964091528258322

def SurrogateDiagonalTailChunk001Sub000Block152Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22783
    = surrogateDiagTailX0RatChunk001Sub000Block152Part019

theorem surrogateDiagonalTailChunk001Sub000Block152Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part019] using hcert

def TailChunk001Sub000Block152Part020SupportExplicit : Finset ℕ :=
  ([22786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part020 : ℚ :=
  (2028132015625 : ℚ) / 10528506576069722112

def SurrogateDiagonalTailChunk001Sub000Block152Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22786
    = surrogateDiagTailX0RatChunk001Sub000Block152Part020

theorem surrogateDiagonalTailChunk001Sub000Block152Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part020] using hcert

def TailChunk001Sub000Block152Part021SupportExplicit : Finset ℕ :=
  ([22787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part021 : ℚ :=
  (8113240140625 : ℚ) / 168515261919137213202

def SurrogateDiagonalTailChunk001Sub000Block152Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22787
    = surrogateDiagTailX0RatChunk001Sub000Block152Part021

theorem surrogateDiagonalTailChunk001Sub000Block152Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part021] using hcert

def TailChunk001Sub000Block152Part022SupportExplicit : Finset ℕ :=
  ([22789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part022 : ℚ :=
  (345860882225 : ℚ) / 6031193073265410048

def SurrogateDiagonalTailChunk001Sub000Block152Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22789
    = surrogateDiagTailX0RatChunk001Sub000Block152Part022

theorem surrogateDiagonalTailChunk001Sub000Block152Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part022] using hcert

def TailChunk001Sub000Block152Part023SupportExplicit : Finset ℕ :=
  ([22790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part023 : ℚ :=
  (191852437475 : ℚ) / 539403296378978304

def SurrogateDiagonalTailChunk001Sub000Block152Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22790
    = surrogateDiagTailX0RatChunk001Sub000Block152Part023

theorem surrogateDiagonalTailChunk001Sub000Block152Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part023] using hcert

def TailChunk001Sub000Block152Part024SupportExplicit : Finset ℕ :=
  ([22791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block152Part024 : ℚ :=
  (69349305899 : ℚ) / 606362684479238400

def SurrogateDiagonalTailChunk001Sub000Block152Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22791
    = surrogateDiagTailX0RatChunk001Sub000Block152Part024

theorem surrogateDiagonalTailChunk001Sub000Block152Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block152Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block152Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block152Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block152Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block152Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block152Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block152HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block152Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block152Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block152Part000
    + surrogateDiagTailX0RatChunk001Sub000Block152Part001
    + surrogateDiagTailX0RatChunk001Sub000Block152Part002
    + surrogateDiagTailX0RatChunk001Sub000Block152Part003
    + surrogateDiagTailX0RatChunk001Sub000Block152Part004
    + surrogateDiagTailX0RatChunk001Sub000Block152Part005
    + surrogateDiagTailX0RatChunk001Sub000Block152Part006
    + surrogateDiagTailX0RatChunk001Sub000Block152Part007
    + surrogateDiagTailX0RatChunk001Sub000Block152Part008
    + surrogateDiagTailX0RatChunk001Sub000Block152Part009

def surrogateDiagonalTailChunk001Sub000Block152MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block152Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block152Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block152Part010
    + surrogateDiagTailX0RatChunk001Sub000Block152Part011
    + surrogateDiagTailX0RatChunk001Sub000Block152Part012
    + surrogateDiagTailX0RatChunk001Sub000Block152Part013
    + surrogateDiagTailX0RatChunk001Sub000Block152Part014
    + surrogateDiagTailX0RatChunk001Sub000Block152Part015
    + surrogateDiagTailX0RatChunk001Sub000Block152Part016
    + surrogateDiagTailX0RatChunk001Sub000Block152Part017
    + surrogateDiagTailX0RatChunk001Sub000Block152Part018
    + surrogateDiagTailX0RatChunk001Sub000Block152Part019

def surrogateDiagonalTailChunk001Sub000Block152TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block152Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block152Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block152Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block152Part020
    + surrogateDiagTailX0RatChunk001Sub000Block152Part021
    + surrogateDiagTailX0RatChunk001Sub000Block152Part022
    + surrogateDiagTailX0RatChunk001Sub000Block152Part023
    + surrogateDiagTailX0RatChunk001Sub000Block152Part024

def surrogateDiagonalTailChunk001Sub000Block152Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block152HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block152MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block152TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block152 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block152Part000
    + surrogateDiagTailX0RatChunk001Sub000Block152Part001
    + surrogateDiagTailX0RatChunk001Sub000Block152Part002
    + surrogateDiagTailX0RatChunk001Sub000Block152Part003
    + surrogateDiagTailX0RatChunk001Sub000Block152Part004
    + surrogateDiagTailX0RatChunk001Sub000Block152Part005
    + surrogateDiagTailX0RatChunk001Sub000Block152Part006
    + surrogateDiagTailX0RatChunk001Sub000Block152Part007
    + surrogateDiagTailX0RatChunk001Sub000Block152Part008
    + surrogateDiagTailX0RatChunk001Sub000Block152Part009
    + surrogateDiagTailX0RatChunk001Sub000Block152Part010
    + surrogateDiagTailX0RatChunk001Sub000Block152Part011
    + surrogateDiagTailX0RatChunk001Sub000Block152Part012
    + surrogateDiagTailX0RatChunk001Sub000Block152Part013
    + surrogateDiagTailX0RatChunk001Sub000Block152Part014
    + surrogateDiagTailX0RatChunk001Sub000Block152Part015
    + surrogateDiagTailX0RatChunk001Sub000Block152Part016
    + surrogateDiagTailX0RatChunk001Sub000Block152Part017
    + surrogateDiagTailX0RatChunk001Sub000Block152Part018
    + surrogateDiagTailX0RatChunk001Sub000Block152Part019
    + surrogateDiagTailX0RatChunk001Sub000Block152Part020
    + surrogateDiagTailX0RatChunk001Sub000Block152Part021
    + surrogateDiagTailX0RatChunk001Sub000Block152Part022
    + surrogateDiagTailX0RatChunk001Sub000Block152Part023
    + surrogateDiagTailX0RatChunk001Sub000Block152Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block152_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block152Head + surrogateDiagTailX0RatChunk001Sub000Block152Mid + surrogateDiagTailX0RatChunk001Sub000Block152Tail =
      surrogateDiagTailX0RatChunk001Sub000Block152 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block152Head surrogateDiagTailX0RatChunk001Sub000Block152Mid surrogateDiagTailX0RatChunk001Sub000Block152Tail surrogateDiagTailX0RatChunk001Sub000Block152
  ring

def SurrogateDiagonalTailChunk001Sub000Block152HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block152HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block152Head

def SurrogateDiagonalTailChunk001Sub000Block152MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block152MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block152Mid

def SurrogateDiagonalTailChunk001Sub000Block152TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block152TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block152Tail

theorem surrogateDiagonalTailChunk001Sub000Block152_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block152HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block152MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block152TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block152Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block152 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block152HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block152MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block152TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block152Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block152_eq_head_add_mid_add_tail

/-- Block 153 covers tail-support indices [13825,13850) and q from 22793 to 22835. -/

def TailChunk001Sub000Block153Part000SupportExplicit : Finset ℕ :=
  ([22793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part000 : ℚ :=
  (119607523351 : ℚ) / 2250703839943437120

def SurrogateDiagonalTailChunk001Sub000Block153Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22793
    = surrogateDiagTailX0RatChunk001Sub000Block153Part000

theorem surrogateDiagonalTailChunk001Sub000Block153Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part000] using hcert

def TailChunk001Sub000Block153Part001SupportExplicit : Finset ℕ :=
  ([22794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part001 : ℚ :=
  (5236077797 : ℚ) / 10805354494771200

def SurrogateDiagonalTailChunk001Sub000Block153Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22794
    = surrogateDiagTailX0RatChunk001Sub000Block153Part001

theorem surrogateDiagonalTailChunk001Sub000Block153Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part001] using hcert

def TailChunk001Sub000Block153Part002SupportExplicit : Finset ℕ :=
  ([22795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part002 : ℚ :=
  (19671491495875 : ℚ) / 243435035745381777408

def SurrogateDiagonalTailChunk001Sub000Block153Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22795
    = surrogateDiagTailX0RatChunk001Sub000Block153Part002

theorem surrogateDiagonalTailChunk001Sub000Block153Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part002] using hcert

def TailChunk001Sub000Block153Part003SupportExplicit : Finset ℕ :=
  ([22798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part003 : ℚ :=
  (2030268765625 : ℚ) / 10550704948217844402

def SurrogateDiagonalTailChunk001Sub000Block153Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22798
    = surrogateDiagTailX0RatChunk001Sub000Block153Part003

theorem surrogateDiagonalTailChunk001Sub000Block153Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part003] using hcert

def TailChunk001Sub000Block153Part004SupportExplicit : Finset ℕ :=
  ([22799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part004 : ℚ :=
  (24519511473025 : ℚ) / 364224742794601463808

def SurrogateDiagonalTailChunk001Sub000Block153Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22799
    = surrogateDiagTailX0RatChunk001Sub000Block153Part004

theorem surrogateDiagonalTailChunk001Sub000Block153Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part004] using hcert

def TailChunk001Sub000Block153Part005SupportExplicit : Finset ℕ :=
  ([22802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part005 : ℚ :=
  (3551389021325 : ℚ) / 15266457466703069184

def SurrogateDiagonalTailChunk001Sub000Block153Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22802
    = surrogateDiagTailX0RatChunk001Sub000Block153Part005

theorem surrogateDiagonalTailChunk001Sub000Block153Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part005] using hcert

def TailChunk001Sub000Block153Part006SupportExplicit : Finset ℕ :=
  ([22803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part006 : ℚ :=
  (162344332793 : ℚ) / 1209154902624000000

def SurrogateDiagonalTailChunk001Sub000Block153Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22803
    = surrogateDiagTailX0RatChunk001Sub000Block153Part006

theorem surrogateDiagonalTailChunk001Sub000Block153Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part006] using hcert

def TailChunk001Sub000Block153Part007SupportExplicit : Finset ℕ :=
  ([22805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part007 : ℚ :=
  (693161675 : ℚ) / 9225819215364096

def SurrogateDiagonalTailChunk001Sub000Block153Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22805
    = surrogateDiagTailX0RatChunk001Sub000Block153Part007

theorem surrogateDiagonalTailChunk001Sub000Block153Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part007] using hcert

def TailChunk001Sub000Block153Part008SupportExplicit : Finset ℕ :=
  ([22807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part008 : ℚ :=
  (8127488265625 : ℚ) / 169107686245006952562

def SurrogateDiagonalTailChunk001Sub000Block153Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22807
    = surrogateDiagTailX0RatChunk001Sub000Block153Part008

theorem surrogateDiagonalTailChunk001Sub000Block153Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part008] using hcert

def TailChunk001Sub000Block153Part009SupportExplicit : Finset ℕ :=
  ([22809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part009 : ℚ :=
  (14448225239725 : ℚ) / 133615949625684505728

def SurrogateDiagonalTailChunk001Sub000Block153Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22809
    = surrogateDiagTailX0RatChunk001Sub000Block153Part009

theorem surrogateDiagonalTailChunk001Sub000Block153Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part009] using hcert

def TailChunk001Sub000Block153Part010SupportExplicit : Finset ℕ :=
  ([22810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part010 : ℚ :=
  (221002807939 : ℚ) / 691936441152307200

def SurrogateDiagonalTailChunk001Sub000Block153Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22810
    = surrogateDiagTailX0RatChunk001Sub000Block153Part010

theorem surrogateDiagonalTailChunk001Sub000Block153Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part010] using hcert

def TailChunk001Sub000Block153Part011SupportExplicit : Finset ℕ :=
  ([22811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part011 : ℚ :=
  (13008543025 : ℚ) / 270762173281545042

def SurrogateDiagonalTailChunk001Sub000Block153Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22811
    = surrogateDiagTailX0RatChunk001Sub000Block153Part011

theorem surrogateDiagonalTailChunk001Sub000Block153Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part011] using hcert

def TailChunk001Sub000Block153Part012SupportExplicit : Finset ℕ :=
  ([22813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part012 : ℚ :=
  (2653848573625 : ℚ) / 40568940973396086912

def SurrogateDiagonalTailChunk001Sub000Block153Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22813
    = surrogateDiagTailX0RatChunk001Sub000Block153Part012

theorem surrogateDiagonalTailChunk001Sub000Block153Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part012] using hcert

def TailChunk001Sub000Block153Part013SupportExplicit : Finset ℕ :=
  ([22814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part013 : ℚ :=
  (245329786651 : ℚ) / 849516429312000000

def SurrogateDiagonalTailChunk001Sub000Block153Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22814
    = surrogateDiagTailX0RatChunk001Sub000Block153Part013

theorem surrogateDiagonalTailChunk001Sub000Block153Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part013] using hcert

def TailChunk001Sub000Block153Part014SupportExplicit : Finset ℕ :=
  ([22817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part014 : ℚ :=
  (8134617015625 : ℚ) / 169404483481784942592

def SurrogateDiagonalTailChunk001Sub000Block153Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22817
    = surrogateDiagTailX0RatChunk001Sub000Block153Part014

theorem surrogateDiagonalTailChunk001Sub000Block153Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part014] using hcert

def TailChunk001Sub000Block153Part015SupportExplicit : Finset ℕ :=
  ([22818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part015 : ℚ :=
  (3614425619725 : ℚ) / 8359788530646092928

def SurrogateDiagonalTailChunk001Sub000Block153Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22818
    = surrogateDiagTailX0RatChunk001Sub000Block153Part015

theorem surrogateDiagonalTailChunk001Sub000Block153Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part015] using hcert

def TailChunk001Sub000Block153Part016SupportExplicit : Finset ℕ :=
  ([22819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part016 : ℚ :=
  (1177497200131 : ℚ) / 21772176924672000000

def SurrogateDiagonalTailChunk001Sub000Block153Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22819
    = surrogateDiagTailX0RatChunk001Sub000Block153Part016

theorem surrogateDiagonalTailChunk001Sub000Block153Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part016] using hcert

def TailChunk001Sub000Block153Part017SupportExplicit : Finset ℕ :=
  ([22821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part017 : ℚ :=
  (14463433239325 : ℚ) / 133897394393161661568

def SurrogateDiagonalTailChunk001Sub000Block153Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22821
    = surrogateDiagTailX0RatChunk001Sub000Block153Part017

theorem surrogateDiagonalTailChunk001Sub000Block153Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part017] using hcert

def TailChunk001Sub000Block153Part018SupportExplicit : Finset ℕ :=
  ([22822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part018 : ℚ :=
  (3255273025 : ℚ) / 16952331169886322

def SurrogateDiagonalTailChunk001Sub000Block153Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22822
    = surrogateDiagTailX0RatChunk001Sub000Block153Part018

theorem surrogateDiagonalTailChunk001Sub000Block153Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part018] using hcert

def TailChunk001Sub000Block153Part019SupportExplicit : Finset ℕ :=
  ([22823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part019 : ℚ :=
  (846548306575 : ℚ) / 16294711200377799168

def SurrogateDiagonalTailChunk001Sub000Block153Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22823
    = surrogateDiagTailX0RatChunk001Sub000Block153Part019

theorem surrogateDiagonalTailChunk001Sub000Block153Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part019] using hcert

def TailChunk001Sub000Block153Part020SupportExplicit : Finset ℕ :=
  ([22826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part020 : ℚ :=
  (15060030381 : ℚ) / 74944479232000000

def SurrogateDiagonalTailChunk001Sub000Block153Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22826
    = surrogateDiagTailX0RatChunk001Sub000Block153Part020

theorem surrogateDiagonalTailChunk001Sub000Block153Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part020] using hcert

def TailChunk001Sub000Block153Part021SupportExplicit : Finset ℕ :=
  ([22827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part021 : ℚ :=
  (10911554234725 : ℚ) / 72122561730481932288

def SurrogateDiagonalTailChunk001Sub000Block153Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22827
    = surrogateDiagTailX0RatChunk001Sub000Block153Part021

theorem surrogateDiagonalTailChunk001Sub000Block153Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part021] using hcert

def TailChunk001Sub000Block153Part022SupportExplicit : Finset ℕ :=
  ([22829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part022 : ℚ :=
  (30915283631125 : ℚ) / 604727488863011340288

def SurrogateDiagonalTailChunk001Sub000Block153Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22829
    = surrogateDiagTailX0RatChunk001Sub000Block153Part022

theorem surrogateDiagonalTailChunk001Sub000Block153Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part022] using hcert

def TailChunk001Sub000Block153Part023SupportExplicit : Finset ℕ :=
  ([22830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part023 : ℚ :=
  (6937307091 : ℚ) / 9111920212705280

def SurrogateDiagonalTailChunk001Sub000Block153Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22830
    = surrogateDiagTailX0RatChunk001Sub000Block153Part023

theorem surrogateDiagonalTailChunk001Sub000Block153Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part023] using hcert

def TailChunk001Sub000Block153Part024SupportExplicit : Finset ℕ :=
  ([22835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block153Part024 : ℚ :=
  (434366796875 : ℚ) / 5796545049230887296

def SurrogateDiagonalTailChunk001Sub000Block153Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22835
    = surrogateDiagTailX0RatChunk001Sub000Block153Part024

theorem surrogateDiagonalTailChunk001Sub000Block153Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block153Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block153Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block153Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block153Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block153Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block153Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block153HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block153Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block153Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block153Part000
    + surrogateDiagTailX0RatChunk001Sub000Block153Part001
    + surrogateDiagTailX0RatChunk001Sub000Block153Part002
    + surrogateDiagTailX0RatChunk001Sub000Block153Part003
    + surrogateDiagTailX0RatChunk001Sub000Block153Part004
    + surrogateDiagTailX0RatChunk001Sub000Block153Part005
    + surrogateDiagTailX0RatChunk001Sub000Block153Part006
    + surrogateDiagTailX0RatChunk001Sub000Block153Part007
    + surrogateDiagTailX0RatChunk001Sub000Block153Part008
    + surrogateDiagTailX0RatChunk001Sub000Block153Part009

def surrogateDiagonalTailChunk001Sub000Block153MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block153Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block153Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block153Part010
    + surrogateDiagTailX0RatChunk001Sub000Block153Part011
    + surrogateDiagTailX0RatChunk001Sub000Block153Part012
    + surrogateDiagTailX0RatChunk001Sub000Block153Part013
    + surrogateDiagTailX0RatChunk001Sub000Block153Part014
    + surrogateDiagTailX0RatChunk001Sub000Block153Part015
    + surrogateDiagTailX0RatChunk001Sub000Block153Part016
    + surrogateDiagTailX0RatChunk001Sub000Block153Part017
    + surrogateDiagTailX0RatChunk001Sub000Block153Part018
    + surrogateDiagTailX0RatChunk001Sub000Block153Part019

def surrogateDiagonalTailChunk001Sub000Block153TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block153Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block153Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block153Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block153Part020
    + surrogateDiagTailX0RatChunk001Sub000Block153Part021
    + surrogateDiagTailX0RatChunk001Sub000Block153Part022
    + surrogateDiagTailX0RatChunk001Sub000Block153Part023
    + surrogateDiagTailX0RatChunk001Sub000Block153Part024

def surrogateDiagonalTailChunk001Sub000Block153Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block153HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block153MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block153TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block153 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block153Part000
    + surrogateDiagTailX0RatChunk001Sub000Block153Part001
    + surrogateDiagTailX0RatChunk001Sub000Block153Part002
    + surrogateDiagTailX0RatChunk001Sub000Block153Part003
    + surrogateDiagTailX0RatChunk001Sub000Block153Part004
    + surrogateDiagTailX0RatChunk001Sub000Block153Part005
    + surrogateDiagTailX0RatChunk001Sub000Block153Part006
    + surrogateDiagTailX0RatChunk001Sub000Block153Part007
    + surrogateDiagTailX0RatChunk001Sub000Block153Part008
    + surrogateDiagTailX0RatChunk001Sub000Block153Part009
    + surrogateDiagTailX0RatChunk001Sub000Block153Part010
    + surrogateDiagTailX0RatChunk001Sub000Block153Part011
    + surrogateDiagTailX0RatChunk001Sub000Block153Part012
    + surrogateDiagTailX0RatChunk001Sub000Block153Part013
    + surrogateDiagTailX0RatChunk001Sub000Block153Part014
    + surrogateDiagTailX0RatChunk001Sub000Block153Part015
    + surrogateDiagTailX0RatChunk001Sub000Block153Part016
    + surrogateDiagTailX0RatChunk001Sub000Block153Part017
    + surrogateDiagTailX0RatChunk001Sub000Block153Part018
    + surrogateDiagTailX0RatChunk001Sub000Block153Part019
    + surrogateDiagTailX0RatChunk001Sub000Block153Part020
    + surrogateDiagTailX0RatChunk001Sub000Block153Part021
    + surrogateDiagTailX0RatChunk001Sub000Block153Part022
    + surrogateDiagTailX0RatChunk001Sub000Block153Part023
    + surrogateDiagTailX0RatChunk001Sub000Block153Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block153_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block153Head + surrogateDiagTailX0RatChunk001Sub000Block153Mid + surrogateDiagTailX0RatChunk001Sub000Block153Tail =
      surrogateDiagTailX0RatChunk001Sub000Block153 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block153Head surrogateDiagTailX0RatChunk001Sub000Block153Mid surrogateDiagTailX0RatChunk001Sub000Block153Tail surrogateDiagTailX0RatChunk001Sub000Block153
  ring

def SurrogateDiagonalTailChunk001Sub000Block153HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block153HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block153Head

def SurrogateDiagonalTailChunk001Sub000Block153MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block153MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block153Mid

def SurrogateDiagonalTailChunk001Sub000Block153TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block153TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block153Tail

theorem surrogateDiagonalTailChunk001Sub000Block153_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block153HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block153MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block153TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block153Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block153 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block153HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block153MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block153TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block153Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block153_eq_head_add_mid_add_tail

/-- Block 154 covers tail-support indices [13850,13875) and q from 22837 to 22874. -/

def TailChunk001Sub000Block154Part000SupportExplicit : Finset ℕ :=
  ([22837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part000 : ℚ :=
  (82887514161 : ℚ) / 1631303330292039680

def SurrogateDiagonalTailChunk001Sub000Block154Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22837
    = surrogateDiagTailX0RatChunk001Sub000Block154Part000

theorem surrogateDiagonalTailChunk001Sub000Block154Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part000] using hcert

def TailChunk001Sub000Block154Part001SupportExplicit : Finset ℕ :=
  ([22838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part001 : ℚ :=
  (299065765711 : ℚ) / 1360761057792000000

def SurrogateDiagonalTailChunk001Sub000Block154Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22838
    = surrogateDiagTailX0RatChunk001Sub000Block154Part001

theorem surrogateDiagonalTailChunk001Sub000Block154Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part001] using hcert

def TailChunk001Sub000Block154Part002SupportExplicit : Finset ℕ :=
  ([22839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part002 : ℚ :=
  (5400890111 : ℚ) / 44907421672396800

def SurrogateDiagonalTailChunk001Sub000Block154Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22839
    = surrogateDiagTailX0RatChunk001Sub000Block154Part002

theorem surrogateDiagonalTailChunk001Sub000Block154Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part002] using hcert

def TailChunk001Sub000Block154Part003SupportExplicit : Finset ℕ :=
  ([22841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part003 : ℚ :=
  (20615516509 : ℚ) / 262492488000000000

def SurrogateDiagonalTailChunk001Sub000Block154Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22841
    = surrogateDiagTailX0RatChunk001Sub000Block154Part003

theorem surrogateDiagonalTailChunk001Sub000Block154Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part003] using hcert

def TailChunk001Sub000Block154Part004SupportExplicit : Finset ℕ :=
  ([22843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part004 : ℚ :=
  (313820498131 : ℚ) / 6250489871108620800

def SurrogateDiagonalTailChunk001Sub000Block154Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22843
    = surrogateDiagTailX0RatChunk001Sub000Block154Part004

theorem surrogateDiagonalTailChunk001Sub000Block154Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part004] using hcert

def TailChunk001Sub000Block154Part005SupportExplicit : Finset ℕ :=
  ([22845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part005 : ℚ :=
  (796416739875 : ℚ) / 4579986211737985024

def SurrogateDiagonalTailChunk001Sub000Block154Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22845
    = surrogateDiagTailX0RatChunk001Sub000Block154Part005

theorem surrogateDiagonalTailChunk001Sub000Block154Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part005] using hcert

def TailChunk001Sub000Block154Part006SupportExplicit : Finset ℕ :=
  ([22846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part006 : ℚ :=
  (2038827015625 : ℚ) / 10639849645434612882

def SurrogateDiagonalTailChunk001Sub000Block154Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22846
    = surrogateDiagTailX0RatChunk001Sub000Block154Part006

theorem surrogateDiagonalTailChunk001Sub000Block154Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part006] using hcert

def TailChunk001Sub000Block154Part007SupportExplicit : Finset ℕ :=
  ([22847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part007 : ℚ :=
  (101038814251 : ℚ) / 1537261006723200000

def SurrogateDiagonalTailChunk001Sub000Block154Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22847
    = surrogateDiagTailX0RatChunk001Sub000Block154Part007

theorem surrogateDiagonalTailChunk001Sub000Block154Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part007] using hcert

def TailChunk001Sub000Block154Part008SupportExplicit : Finset ℕ :=
  ([22849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part008 : ℚ :=
  (31655066635225 : ℚ) / 636759188629050359808

def SurrogateDiagonalTailChunk001Sub000Block154Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22849
    = surrogateDiagTailX0RatChunk001Sub000Block154Part008

theorem surrogateDiagonalTailChunk001Sub000Block154Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part008] using hcert

def TailChunk001Sub000Block154Part009SupportExplicit : Finset ℕ :=
  ([22853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part009 : ℚ :=
  (8160306390625 : ℚ) / 170476189377017125152

def SurrogateDiagonalTailChunk001Sub000Block154Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22853
    = surrogateDiagTailX0RatChunk001Sub000Block154Part009

theorem surrogateDiagonalTailChunk001Sub000Block154Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part009] using hcert

def TailChunk001Sub000Block154Part010SupportExplicit : Finset ℕ :=
  ([22854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part010 : ℚ :=
  (1080712826525 : ℚ) / 2010397691088470016

def SurrogateDiagonalTailChunk001Sub000Block154Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22854
    = surrogateDiagTailX0RatChunk001Sub000Block154Part010

theorem surrogateDiagonalTailChunk001Sub000Block154Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part010] using hcert

def TailChunk001Sub000Block154Part011SupportExplicit : Finset ℕ :=
  ([22855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part011 : ℚ :=
  (15495174344125 : ℚ) / 149920909653516484608

def SurrogateDiagonalTailChunk001Sub000Block154Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22855
    = surrogateDiagTailX0RatChunk001Sub000Block154Part011

theorem surrogateDiagonalTailChunk001Sub000Block154Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part011] using hcert

def TailChunk001Sub000Block154Part012SupportExplicit : Finset ℕ :=
  ([22857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part012 : ℚ :=
  (527230722253 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub000Block154Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22857
    = surrogateDiagTailX0RatChunk001Sub000Block154Part012

theorem surrogateDiagonalTailChunk001Sub000Block154Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part012] using hcert

def TailChunk001Sub000Block154Part013SupportExplicit : Finset ℕ :=
  ([22858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part013 : ℚ :=
  (280296940609 : ℚ) / 1161117750250627200

def SurrogateDiagonalTailChunk001Sub000Block154Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22858
    = surrogateDiagTailX0RatChunk001Sub000Block154Part013

theorem surrogateDiagonalTailChunk001Sub000Block154Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part013] using hcert

def TailChunk001Sub000Block154Part014SupportExplicit : Finset ℕ :=
  ([22859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part014 : ℚ :=
  (8164591890625 : ℚ) / 170655300185246821362

def SurrogateDiagonalTailChunk001Sub000Block154Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22859
    = surrogateDiagTailX0RatChunk001Sub000Block154Part014

theorem surrogateDiagonalTailChunk001Sub000Block154Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part014] using hcert

def TailChunk001Sub000Block154Part015SupportExplicit : Finset ℕ :=
  ([22861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part015 : ℚ :=
  (13065633025 : ℚ) / 273144056223827232

def SurrogateDiagonalTailChunk001Sub000Block154Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22861
    = surrogateDiagTailX0RatChunk001Sub000Block154Part015

theorem surrogateDiagonalTailChunk001Sub000Block154Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part015] using hcert

def TailChunk001Sub000Block154Part016SupportExplicit : Finset ℕ :=
  ([22862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part016 : ℚ :=
  (231606709921 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk001Sub000Block154Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22862
    = surrogateDiagTailX0RatChunk001Sub000Block154Part016

theorem surrogateDiagonalTailChunk001Sub000Block154Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part016] using hcert

def TailChunk001Sub000Block154Part017SupportExplicit : Finset ℕ :=
  ([22863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part017 : ℚ :=
  (580668969517 : ℚ) / 5395438147631155200

def SurrogateDiagonalTailChunk001Sub000Block154Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22863
    = surrogateDiagTailX0RatChunk001Sub000Block154Part017

theorem surrogateDiagonalTailChunk001Sub000Block154Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part017] using hcert

def TailChunk001Sub000Block154Part018SupportExplicit : Finset ℕ :=
  ([22865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part018 : ℚ :=
  (18689215780225 : ℚ) / 216414288384683409408

def SurrogateDiagonalTailChunk001Sub000Block154Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22865
    = surrogateDiagTailX0RatChunk001Sub000Block154Part018

theorem surrogateDiagonalTailChunk001Sub000Block154Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part018] using hcert

def TailChunk001Sub000Block154Part019SupportExplicit : Finset ℕ :=
  ([22866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part019 : ℚ :=
  (1726415943725 : ℚ) / 3636867977851060224

def SurrogateDiagonalTailChunk001Sub000Block154Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22866
    = surrogateDiagTailX0RatChunk001Sub000Block154Part019

theorem surrogateDiagonalTailChunk001Sub000Block154Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part019] using hcert

def TailChunk001Sub000Block154Part020SupportExplicit : Finset ℕ :=
  ([22867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part020 : ℚ :=
  (3134101784525 : ℚ) / 55028137854318446592

def SurrogateDiagonalTailChunk001Sub000Block154Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22867
    = surrogateDiagTailX0RatChunk001Sub000Block154Part020

theorem surrogateDiagonalTailChunk001Sub000Block154Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part020] using hcert

def TailChunk001Sub000Block154Part021SupportExplicit : Finset ℕ :=
  ([22870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part021 : ℚ :=
  (5554181188525 : ℚ) / 17481219598324942848

def SurrogateDiagonalTailChunk001Sub000Block154Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22870
    = surrogateDiagTailX0RatChunk001Sub000Block154Part021

theorem surrogateDiagonalTailChunk001Sub000Block154Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part021] using hcert

def TailChunk001Sub000Block154Part022SupportExplicit : Finset ℕ :=
  ([22871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part022 : ℚ :=
  (13077066025 : ℚ) / 273622312281362322

def SurrogateDiagonalTailChunk001Sub000Block154Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22871
    = surrogateDiagTailX0RatChunk001Sub000Block154Part022

theorem surrogateDiagonalTailChunk001Sub000Block154Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part022] using hcert

def TailChunk001Sub000Block154Part023SupportExplicit : Finset ℕ :=
  ([22873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part023 : ℚ :=
  (31822914803725 : ℚ) / 644046773288674787328

def SurrogateDiagonalTailChunk001Sub000Block154Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22873
    = surrogateDiagTailX0RatChunk001Sub000Block154Part023

theorem surrogateDiagonalTailChunk001Sub000Block154Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part023] using hcert

def TailChunk001Sub000Block154Part024SupportExplicit : Finset ℕ :=
  ([22874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block154Part024 : ℚ :=
  (2043827640625 : ℚ) / 10692110890925029152

def SurrogateDiagonalTailChunk001Sub000Block154Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22874
    = surrogateDiagTailX0RatChunk001Sub000Block154Part024

theorem surrogateDiagonalTailChunk001Sub000Block154Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block154Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block154Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block154Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block154Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block154Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block154Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block154HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block154Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block154Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block154Part000
    + surrogateDiagTailX0RatChunk001Sub000Block154Part001
    + surrogateDiagTailX0RatChunk001Sub000Block154Part002
    + surrogateDiagTailX0RatChunk001Sub000Block154Part003
    + surrogateDiagTailX0RatChunk001Sub000Block154Part004
    + surrogateDiagTailX0RatChunk001Sub000Block154Part005
    + surrogateDiagTailX0RatChunk001Sub000Block154Part006
    + surrogateDiagTailX0RatChunk001Sub000Block154Part007
    + surrogateDiagTailX0RatChunk001Sub000Block154Part008
    + surrogateDiagTailX0RatChunk001Sub000Block154Part009

def surrogateDiagonalTailChunk001Sub000Block154MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block154Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block154Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block154Part010
    + surrogateDiagTailX0RatChunk001Sub000Block154Part011
    + surrogateDiagTailX0RatChunk001Sub000Block154Part012
    + surrogateDiagTailX0RatChunk001Sub000Block154Part013
    + surrogateDiagTailX0RatChunk001Sub000Block154Part014
    + surrogateDiagTailX0RatChunk001Sub000Block154Part015
    + surrogateDiagTailX0RatChunk001Sub000Block154Part016
    + surrogateDiagTailX0RatChunk001Sub000Block154Part017
    + surrogateDiagTailX0RatChunk001Sub000Block154Part018
    + surrogateDiagTailX0RatChunk001Sub000Block154Part019

def surrogateDiagonalTailChunk001Sub000Block154TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block154Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block154Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block154Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block154Part020
    + surrogateDiagTailX0RatChunk001Sub000Block154Part021
    + surrogateDiagTailX0RatChunk001Sub000Block154Part022
    + surrogateDiagTailX0RatChunk001Sub000Block154Part023
    + surrogateDiagTailX0RatChunk001Sub000Block154Part024

def surrogateDiagonalTailChunk001Sub000Block154Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block154HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block154MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block154TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block154 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block154Part000
    + surrogateDiagTailX0RatChunk001Sub000Block154Part001
    + surrogateDiagTailX0RatChunk001Sub000Block154Part002
    + surrogateDiagTailX0RatChunk001Sub000Block154Part003
    + surrogateDiagTailX0RatChunk001Sub000Block154Part004
    + surrogateDiagTailX0RatChunk001Sub000Block154Part005
    + surrogateDiagTailX0RatChunk001Sub000Block154Part006
    + surrogateDiagTailX0RatChunk001Sub000Block154Part007
    + surrogateDiagTailX0RatChunk001Sub000Block154Part008
    + surrogateDiagTailX0RatChunk001Sub000Block154Part009
    + surrogateDiagTailX0RatChunk001Sub000Block154Part010
    + surrogateDiagTailX0RatChunk001Sub000Block154Part011
    + surrogateDiagTailX0RatChunk001Sub000Block154Part012
    + surrogateDiagTailX0RatChunk001Sub000Block154Part013
    + surrogateDiagTailX0RatChunk001Sub000Block154Part014
    + surrogateDiagTailX0RatChunk001Sub000Block154Part015
    + surrogateDiagTailX0RatChunk001Sub000Block154Part016
    + surrogateDiagTailX0RatChunk001Sub000Block154Part017
    + surrogateDiagTailX0RatChunk001Sub000Block154Part018
    + surrogateDiagTailX0RatChunk001Sub000Block154Part019
    + surrogateDiagTailX0RatChunk001Sub000Block154Part020
    + surrogateDiagTailX0RatChunk001Sub000Block154Part021
    + surrogateDiagTailX0RatChunk001Sub000Block154Part022
    + surrogateDiagTailX0RatChunk001Sub000Block154Part023
    + surrogateDiagTailX0RatChunk001Sub000Block154Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block154_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block154Head + surrogateDiagTailX0RatChunk001Sub000Block154Mid + surrogateDiagTailX0RatChunk001Sub000Block154Tail =
      surrogateDiagTailX0RatChunk001Sub000Block154 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block154Head surrogateDiagTailX0RatChunk001Sub000Block154Mid surrogateDiagTailX0RatChunk001Sub000Block154Tail surrogateDiagTailX0RatChunk001Sub000Block154
  ring

def SurrogateDiagonalTailChunk001Sub000Block154HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block154HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block154Head

def SurrogateDiagonalTailChunk001Sub000Block154MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block154MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block154Mid

def SurrogateDiagonalTailChunk001Sub000Block154TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block154TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block154Tail

theorem surrogateDiagonalTailChunk001Sub000Block154_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block154HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block154MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block154TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block154Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block154 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block154HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block154MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block154TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block154Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block154_eq_head_add_mid_add_tail

/-- Block 155 covers tail-support indices [13875,13900) and q from 22877 to 22917. -/

def TailChunk001Sub000Block155Part000SupportExplicit : Finset ℕ :=
  ([22877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part000 : ℚ :=
  (8177455140625 : ℚ) / 171193479506414736672

def SurrogateDiagonalTailChunk001Sub000Block155Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22877
    = surrogateDiagTailX0RatChunk001Sub000Block155Part000

theorem surrogateDiagonalTailChunk001Sub000Block155Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part000] using hcert

def TailChunk001Sub000Block155Part001SupportExplicit : Finset ℕ :=
  ([22879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part001 : ℚ :=
  (7986809215975 : ℚ) / 162388344075331510272

def SurrogateDiagonalTailChunk001Sub000Block155Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22879
    = surrogateDiagTailX0RatChunk001Sub000Block155Part001

theorem surrogateDiagonalTailChunk001Sub000Block155Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part001] using hcert

def TailChunk001Sub000Block155Part002SupportExplicit : Finset ℕ :=
  ([22881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part002 : ℚ :=
  (4541962833825 : ℚ) / 38624500623117746176

def SurrogateDiagonalTailChunk001Sub000Block155Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22881
    = surrogateDiagTailX0RatChunk001Sub000Block155Part002

theorem surrogateDiagonalTailChunk001Sub000Block155Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part002] using hcert

def TailChunk001Sub000Block155Part003SupportExplicit : Finset ℕ :=
  ([22882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part003 : ℚ :=
  (176879054375 : ℚ) / 795672945333633024

def SurrogateDiagonalTailChunk001Sub000Block155Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22882
    = surrogateDiagTailX0RatChunk001Sub000Block155Part003

theorem surrogateDiagonalTailChunk001Sub000Block155Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part003] using hcert

def TailChunk001Sub000Block155Part004SupportExplicit : Finset ℕ :=
  ([22885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part004 : ℚ :=
  (6402491552675 : ℚ) / 76824024403402653696

def SurrogateDiagonalTailChunk001Sub000Block155Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22885
    = surrogateDiagTailX0RatChunk001Sub000Block155Part004

theorem surrogateDiagonalTailChunk001Sub000Block155Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part004] using hcert

def TailChunk001Sub000Block155Part005SupportExplicit : Finset ℕ :=
  ([22886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part005 : ℚ :=
  (2045972640625 : ℚ) / 10714567403836580562

def SurrogateDiagonalTailChunk001Sub000Block155Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22886
    = surrogateDiagTailX0RatChunk001Sub000Block155Part005

theorem surrogateDiagonalTailChunk001Sub000Block155Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part005] using hcert

def TailChunk001Sub000Block155Part006SupportExplicit : Finset ℕ :=
  ([22889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part006 : ℚ :=
  (1364616632675 : ℚ) / 27156601950802171776

def SurrogateDiagonalTailChunk001Sub000Block155Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22889
    = surrogateDiagTailX0RatChunk001Sub000Block155Part006

theorem surrogateDiagonalTailChunk001Sub000Block155Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part006] using hcert

def TailChunk001Sub000Block155Part007SupportExplicit : Finset ℕ :=
  ([22890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part007 : ℚ :=
  (88118099575 : ℚ) / 75244643451666432

def SurrogateDiagonalTailChunk001Sub000Block155Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22890
    = surrogateDiagTailX0RatChunk001Sub000Block155Part007

theorem surrogateDiagonalTailChunk001Sub000Block155Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part007] using hcert

def TailChunk001Sub000Block155Part008SupportExplicit : Finset ℕ :=
  ([22891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part008 : ℚ :=
  (54629202893 : ℚ) / 936074025369600000

def SurrogateDiagonalTailChunk001Sub000Block155Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22891
    = surrogateDiagTailX0RatChunk001Sub000Block155Part008

theorem surrogateDiagonalTailChunk001Sub000Block155Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part008] using hcert

def TailChunk001Sub000Block155Part009SupportExplicit : Finset ℕ :=
  ([22893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part009 : ℚ :=
  (12669806154925 : ℚ) / 97827800629899460608

def SurrogateDiagonalTailChunk001Sub000Block155Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22893
    = surrogateDiagTailX0RatChunk001Sub000Block155Part009

theorem surrogateDiagonalTailChunk001Sub000Block155Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part009] using hcert

def TailChunk001Sub000Block155Part010SupportExplicit : Finset ℕ :=
  ([22894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part010 : ℚ :=
  (2047403265625 : ℚ) / 10729558051988304882

def SurrogateDiagonalTailChunk001Sub000Block155Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22894
    = surrogateDiagTailX0RatChunk001Sub000Block155Part010

theorem surrogateDiagonalTailChunk001Sub000Block155Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part010] using hcert

def TailChunk001Sub000Block155Part011SupportExplicit : Finset ℕ :=
  ([22895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part011 : ℚ :=
  (189723818809 : ℚ) / 2229470917086412800

def SurrogateDiagonalTailChunk001Sub000Block155Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22895
    = surrogateDiagTailX0RatChunk001Sub000Block155Part011

theorem surrogateDiagonalTailChunk001Sub000Block155Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part011] using hcert

def TailChunk001Sub000Block155Part012SupportExplicit : Finset ℕ :=
  ([22897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part012 : ℚ :=
  (197846435309 : ℚ) / 2964236550591565440

def SurrogateDiagonalTailChunk001Sub000Block155Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22897
    = surrogateDiagTailX0RatChunk001Sub000Block155Part012

theorem surrogateDiagonalTailChunk001Sub000Block155Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part012] using hcert

def TailChunk001Sub000Block155Part013SupportExplicit : Finset ℕ :=
  ([22899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part013 : ℚ :=
  (4351678859025 : ℚ) / 35206072050317787136

def SurrogateDiagonalTailChunk001Sub000Block155Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22899
    = surrogateDiagTailX0RatChunk001Sub000Block155Part013

theorem surrogateDiagonalTailChunk001Sub000Block155Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part013] using hcert

def TailChunk001Sub000Block155Part014SupportExplicit : Finset ℕ :=
  ([22901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part014 : ℚ :=
  (524455801 : ℚ) / 11002433970784800

def SurrogateDiagonalTailChunk001Sub000Block155Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22901
    = surrogateDiagTailX0RatChunk001Sub000Block155Part014

theorem surrogateDiagonalTailChunk001Sub000Block155Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part014] using hcert

def TailChunk001Sub000Block155Part015SupportExplicit : Finset ℕ :=
  ([22902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part015 : ℚ :=
  (31480129493 : ℚ) / 45871318528419840

def SurrogateDiagonalTailChunk001Sub000Block155Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22902
    = surrogateDiagTailX0RatChunk001Sub000Block155Part015

theorem surrogateDiagonalTailChunk001Sub000Block155Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part015] using hcert

def TailChunk001Sub000Block155Part016SupportExplicit : Finset ℕ :=
  ([22903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part016 : ℚ :=
  (31116285583075 : ℚ) / 612619423539926059008

def SurrogateDiagonalTailChunk001Sub000Block155Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22903
    = surrogateDiagTailX0RatChunk001Sub000Block155Part016

theorem surrogateDiagonalTailChunk001Sub000Block155Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part016] using hcert

def TailChunk001Sub000Block155Part017SupportExplicit : Finset ℕ :=
  ([22906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part017 : ℚ :=
  (288652498969 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk001Sub000Block155Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22906
    = surrogateDiagTailX0RatChunk001Sub000Block155Part017

theorem surrogateDiagonalTailChunk001Sub000Block155Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part017] using hcert

def TailChunk001Sub000Block155Part018SupportExplicit : Finset ℕ :=
  ([22907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part018 : ℚ :=
  (8198916390625 : ℚ) / 172093272477357853362

def SurrogateDiagonalTailChunk001Sub000Block155Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22907
    = surrogateDiagTailX0RatChunk001Sub000Block155Part018

theorem surrogateDiagonalTailChunk001Sub000Block155Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part018] using hcert

def TailChunk001Sub000Block155Part019SupportExplicit : Finset ℕ :=
  ([22909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part019 : ℚ :=
  (1234080082891 : ℚ) / 24032409546421123200

def SurrogateDiagonalTailChunk001Sub000Block155Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22909
    = surrogateDiagTailX0RatChunk001Sub000Block155Part019

theorem surrogateDiagonalTailChunk001Sub000Block155Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part019] using hcert

def TailChunk001Sub000Block155Part020SupportExplicit : Finset ℕ :=
  ([22910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part020 : ℚ :=
  (9017109625 : ℚ) / 25284529517764608

def SurrogateDiagonalTailChunk001Sub000Block155Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22910
    = surrogateDiagTailX0RatChunk001Sub000Block155Part020

theorem surrogateDiagonalTailChunk001Sub000Block155Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part020] using hcert

def TailChunk001Sub000Block155Part021SupportExplicit : Finset ℕ :=
  ([22911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part021 : ℚ :=
  (85974251 : ℚ) / 564745570528800

def SurrogateDiagonalTailChunk001Sub000Block155Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22911
    = surrogateDiagTailX0RatChunk001Sub000Block155Part021

theorem surrogateDiagonalTailChunk001Sub000Block155Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part021] using hcert

def TailChunk001Sub000Block155Part022SupportExplicit : Finset ℕ :=
  ([22913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part022 : ℚ :=
  (109468595101 : ℚ) / 1879359012260723520

def SurrogateDiagonalTailChunk001Sub000Block155Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22913
    = surrogateDiagTailX0RatChunk001Sub000Block155Part022

theorem surrogateDiagonalTailChunk001Sub000Block155Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part022] using hcert

def TailChunk001Sub000Block155Part023SupportExplicit : Finset ℕ :=
  ([22915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part023 : ℚ :=
  (1312248390625 : ℚ) / 17634663660933729408

def SurrogateDiagonalTailChunk001Sub000Block155Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22915
    = surrogateDiagTailX0RatChunk001Sub000Block155Part023

theorem surrogateDiagonalTailChunk001Sub000Block155Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part023] using hcert

def TailChunk001Sub000Block155Part024SupportExplicit : Finset ℕ :=
  ([22917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block155Part024 : ℚ :=
  (14585385236125 : ℚ) / 136164989745796111488

def SurrogateDiagonalTailChunk001Sub000Block155Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22917
    = surrogateDiagTailX0RatChunk001Sub000Block155Part024

theorem surrogateDiagonalTailChunk001Sub000Block155Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block155Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block155Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block155Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block155Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block155Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block155Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block155HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block155Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block155Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block155Part000
    + surrogateDiagTailX0RatChunk001Sub000Block155Part001
    + surrogateDiagTailX0RatChunk001Sub000Block155Part002
    + surrogateDiagTailX0RatChunk001Sub000Block155Part003
    + surrogateDiagTailX0RatChunk001Sub000Block155Part004
    + surrogateDiagTailX0RatChunk001Sub000Block155Part005
    + surrogateDiagTailX0RatChunk001Sub000Block155Part006
    + surrogateDiagTailX0RatChunk001Sub000Block155Part007
    + surrogateDiagTailX0RatChunk001Sub000Block155Part008
    + surrogateDiagTailX0RatChunk001Sub000Block155Part009

def surrogateDiagonalTailChunk001Sub000Block155MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block155Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block155Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block155Part010
    + surrogateDiagTailX0RatChunk001Sub000Block155Part011
    + surrogateDiagTailX0RatChunk001Sub000Block155Part012
    + surrogateDiagTailX0RatChunk001Sub000Block155Part013
    + surrogateDiagTailX0RatChunk001Sub000Block155Part014
    + surrogateDiagTailX0RatChunk001Sub000Block155Part015
    + surrogateDiagTailX0RatChunk001Sub000Block155Part016
    + surrogateDiagTailX0RatChunk001Sub000Block155Part017
    + surrogateDiagTailX0RatChunk001Sub000Block155Part018
    + surrogateDiagTailX0RatChunk001Sub000Block155Part019

def surrogateDiagonalTailChunk001Sub000Block155TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block155Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block155Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block155Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block155Part020
    + surrogateDiagTailX0RatChunk001Sub000Block155Part021
    + surrogateDiagTailX0RatChunk001Sub000Block155Part022
    + surrogateDiagTailX0RatChunk001Sub000Block155Part023
    + surrogateDiagTailX0RatChunk001Sub000Block155Part024

def surrogateDiagonalTailChunk001Sub000Block155Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block155HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block155MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block155TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block155 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block155Part000
    + surrogateDiagTailX0RatChunk001Sub000Block155Part001
    + surrogateDiagTailX0RatChunk001Sub000Block155Part002
    + surrogateDiagTailX0RatChunk001Sub000Block155Part003
    + surrogateDiagTailX0RatChunk001Sub000Block155Part004
    + surrogateDiagTailX0RatChunk001Sub000Block155Part005
    + surrogateDiagTailX0RatChunk001Sub000Block155Part006
    + surrogateDiagTailX0RatChunk001Sub000Block155Part007
    + surrogateDiagTailX0RatChunk001Sub000Block155Part008
    + surrogateDiagTailX0RatChunk001Sub000Block155Part009
    + surrogateDiagTailX0RatChunk001Sub000Block155Part010
    + surrogateDiagTailX0RatChunk001Sub000Block155Part011
    + surrogateDiagTailX0RatChunk001Sub000Block155Part012
    + surrogateDiagTailX0RatChunk001Sub000Block155Part013
    + surrogateDiagTailX0RatChunk001Sub000Block155Part014
    + surrogateDiagTailX0RatChunk001Sub000Block155Part015
    + surrogateDiagTailX0RatChunk001Sub000Block155Part016
    + surrogateDiagTailX0RatChunk001Sub000Block155Part017
    + surrogateDiagTailX0RatChunk001Sub000Block155Part018
    + surrogateDiagTailX0RatChunk001Sub000Block155Part019
    + surrogateDiagTailX0RatChunk001Sub000Block155Part020
    + surrogateDiagTailX0RatChunk001Sub000Block155Part021
    + surrogateDiagTailX0RatChunk001Sub000Block155Part022
    + surrogateDiagTailX0RatChunk001Sub000Block155Part023
    + surrogateDiagTailX0RatChunk001Sub000Block155Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block155_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block155Head + surrogateDiagTailX0RatChunk001Sub000Block155Mid + surrogateDiagTailX0RatChunk001Sub000Block155Tail =
      surrogateDiagTailX0RatChunk001Sub000Block155 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block155Head surrogateDiagTailX0RatChunk001Sub000Block155Mid surrogateDiagTailX0RatChunk001Sub000Block155Tail surrogateDiagTailX0RatChunk001Sub000Block155
  ring

def SurrogateDiagonalTailChunk001Sub000Block155HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block155HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block155Head

def SurrogateDiagonalTailChunk001Sub000Block155MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block155MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block155Mid

def SurrogateDiagonalTailChunk001Sub000Block155TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block155TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block155Tail

theorem surrogateDiagonalTailChunk001Sub000Block155_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block155HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block155MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block155TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block155Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block155 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block155HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block155MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block155TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block155Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block155_eq_head_add_mid_add_tail

/-- Block 156 covers tail-support indices [13900,13925) and q from 22918 to 22955. -/

def TailChunk001Sub000Block156Part000SupportExplicit : Finset ℕ :=
  ([22918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part000 : ℚ :=
  (1589821331875 : ℚ) / 5803701486988718592

def SurrogateDiagonalTailChunk001Sub000Block156Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22918
    = surrogateDiagTailX0RatChunk001Sub000Block156Part000

theorem surrogateDiagonalTailChunk001Sub000Block156Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part000] using hcert

def TailChunk001Sub000Block156Part001SupportExplicit : Finset ℕ :=
  ([22919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part001 : ℚ :=
  (104096832139 : ℚ) / 1652148046890270720

def SurrogateDiagonalTailChunk001Sub000Block156Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22919
    = surrogateDiagTailX0RatChunk001Sub000Block156Part001

theorem surrogateDiagonalTailChunk001Sub000Block156Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part001] using hcert

def TailChunk001Sub000Block156Part002SupportExplicit : Finset ℕ :=
  ([22921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part002 : ℚ :=
  (13134306025 : ℚ) / 276023020102267392

def SurrogateDiagonalTailChunk001Sub000Block156Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22921
    = surrogateDiagTailX0RatChunk001Sub000Block156Part002

theorem surrogateDiagonalTailChunk001Sub000Block156Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part002] using hcert

def TailChunk001Sub000Block156Part003SupportExplicit : Finset ℕ :=
  ([22922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part003 : ℚ :=
  (294633195275 : ℚ) / 1473979603307986944

def SurrogateDiagonalTailChunk001Sub000Block156Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22922
    = surrogateDiagTailX0RatChunk001Sub000Block156Part003

theorem surrogateDiagonalTailChunk001Sub000Block156Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part003] using hcert

def TailChunk001Sub000Block156Part004SupportExplicit : Finset ℕ :=
  ([22926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part004 : ℚ :=
  (91229589239 : ℚ) / 170384580310041600

def SurrogateDiagonalTailChunk001Sub000Block156Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22926
    = surrogateDiagTailX0RatChunk001Sub000Block156Part004

theorem surrogateDiagonalTailChunk001Sub000Block156Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part004] using hcert

def TailChunk001Sub000Block156Part005SupportExplicit : Finset ℕ :=
  ([22927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part005 : ℚ :=
  (256183012007 : ℚ) / 5218559055110400000

def SurrogateDiagonalTailChunk001Sub000Block156Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22927
    = surrogateDiagTailX0RatChunk001Sub000Block156Part005

theorem surrogateDiagonalTailChunk001Sub000Block156Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part005] using hcert

def TailChunk001Sub000Block156Part006SupportExplicit : Finset ℕ :=
  ([22929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part006 : ℚ :=
  (14600665235725 : ℚ) / 136450450842317655168

def SurrogateDiagonalTailChunk001Sub000Block156Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22929
    = surrogateDiagTailX0RatChunk001Sub000Block156Part006

theorem surrogateDiagonalTailChunk001Sub000Block156Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part006] using hcert

def TailChunk001Sub000Block156Part007SupportExplicit : Finset ℕ :=
  ([22930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part007 : ℚ :=
  (5583368685775 : ℚ) / 17665473286545113088

def SurrogateDiagonalTailChunk001Sub000Block156Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22930
    = surrogateDiagTailX0RatChunk001Sub000Block156Part007

theorem surrogateDiagonalTailChunk001Sub000Block156Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part007] using hcert

def TailChunk001Sub000Block156Part008SupportExplicit : Finset ℕ :=
  ([22931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part008 : ℚ :=
  (1375697417725 : ℚ) / 26201868037837138944

def SurrogateDiagonalTailChunk001Sub000Block156Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22931
    = surrogateDiagTailX0RatChunk001Sub000Block156Part008

theorem surrogateDiagonalTailChunk001Sub000Block156Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part008] using hcert

def TailChunk001Sub000Block156Part009SupportExplicit : Finset ℕ :=
  ([22933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part009 : ℚ :=
  (43404204131 : ℚ) / 688395019537612800

def SurrogateDiagonalTailChunk001Sub000Block156Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22933
    = surrogateDiagTailX0RatChunk001Sub000Block156Part009

theorem surrogateDiagonalTailChunk001Sub000Block156Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part009] using hcert

def TailChunk001Sub000Block156Part010SupportExplicit : Finset ℕ :=
  ([22934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part010 : ℚ :=
  (2054563890625 : ℚ) / 10804747379467629042

def SurrogateDiagonalTailChunk001Sub000Block156Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22934
    = surrogateDiagTailX0RatChunk001Sub000Block156Part010

theorem surrogateDiagonalTailChunk001Sub000Block156Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part010] using hcert

def TailChunk001Sub000Block156Part011SupportExplicit : Finset ℕ :=
  ([22935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part011 : ℚ :=
  (36320709301 : ℚ) / 165089949371596800

def SurrogateDiagonalTailChunk001Sub000Block156Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22935
    = surrogateDiagTailX0RatChunk001Sub000Block156Part011

theorem surrogateDiagonalTailChunk001Sub000Block156Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part011] using hcert

def TailChunk001Sub000Block156Part012SupportExplicit : Finset ℕ :=
  ([22937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part012 : ℚ :=
  (8220405765625 : ℚ) / 172996607780281201152

def SurrogateDiagonalTailChunk001Sub000Block156Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22937
    = surrogateDiagTailX0RatChunk001Sub000Block156Part012

theorem surrogateDiagonalTailChunk001Sub000Block156Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part012] using hcert

def TailChunk001Sub000Block156Part013SupportExplicit : Finset ℕ :=
  ([22938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part013 : ℚ :=
  (1141564119025 : ℚ) / 2134271087302247712

def SurrogateDiagonalTailChunk001Sub000Block156Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22938
    = surrogateDiagTailX0RatChunk001Sub000Block156Part013

theorem surrogateDiagonalTailChunk001Sub000Block156Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part013] using hcert

def TailChunk001Sub000Block156Part014SupportExplicit : Finset ℕ :=
  ([22939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part014 : ℚ :=
  (5740951389175 : ℚ) / 78356690579427950592

def SurrogateDiagonalTailChunk001Sub000Block156Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22939
    = surrogateDiagTailX0RatChunk001Sub000Block156Part014

theorem surrogateDiagonalTailChunk001Sub000Block156Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part014] using hcert

def TailChunk001Sub000Block156Part015SupportExplicit : Finset ℕ :=
  ([22942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part015 : ℚ :=
  (3289596025 : ℚ) / 17311732062891762

def SurrogateDiagonalTailChunk001Sub000Block156Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22942
    = surrogateDiagTailX0RatChunk001Sub000Block156Part015

theorem surrogateDiagonalTailChunk001Sub000Block156Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part015] using hcert

def TailChunk001Sub000Block156Part016SupportExplicit : Finset ℕ :=
  ([22943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part016 : ℚ :=
  (8224707015625 : ℚ) / 173177700737557436562

def SurrogateDiagonalTailChunk001Sub000Block156Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22943
    = surrogateDiagTailX0RatChunk001Sub000Block156Part016

theorem surrogateDiagonalTailChunk001Sub000Block156Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part016] using hcert

def TailChunk001Sub000Block156Part017SupportExplicit : Finset ℕ :=
  ([22945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part017 : ℚ :=
  (19299028074775 : ℚ) / 203780424360869756928

def SurrogateDiagonalTailChunk001Sub000Block156Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22945
    = surrogateDiagTailX0RatChunk001Sub000Block156Part017

theorem surrogateDiagonalTailChunk001Sub000Block156Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part017] using hcert

def TailChunk001Sub000Block156Part018SupportExplicit : Finset ℕ :=
  ([22946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part018 : ℚ :=
  (218215817929 : ℚ) / 621926000263987200

def SurrogateDiagonalTailChunk001Sub000Block156Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22946
    = surrogateDiagTailX0RatChunk001Sub000Block156Part018

theorem surrogateDiagonalTailChunk001Sub000Block156Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part018] using hcert

def TailChunk001Sub000Block156Part019SupportExplicit : Finset ℕ :=
  ([22947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part019 : ℚ :=
  (14623600235125 : ℚ) / 136879483764477001728

def SurrogateDiagonalTailChunk001Sub000Block156Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22947
    = surrogateDiagTailX0RatChunk001Sub000Block156Part019

theorem surrogateDiagonalTailChunk001Sub000Block156Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part019] using hcert

def TailChunk001Sub000Block156Part020SupportExplicit : Finset ℕ :=
  ([22949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part020 : ℚ :=
  (31686364190875 : ℚ) / 636759188629050359808

def SurrogateDiagonalTailChunk001Sub000Block156Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22949
    = surrogateDiagTailX0RatChunk001Sub000Block156Part020

theorem surrogateDiagonalTailChunk001Sub000Block156Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part020] using hcert

def TailChunk001Sub000Block156Part021SupportExplicit : Finset ℕ :=
  ([22951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part021 : ℚ :=
  (2648759322525 : ℚ) / 53442219870412793344

def SurrogateDiagonalTailChunk001Sub000Block156Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22951
    = surrogateDiagTailX0RatChunk001Sub000Block156Part021

theorem surrogateDiagonalTailChunk001Sub000Block156Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part021] using hcert

def TailChunk001Sub000Block156Part022SupportExplicit : Finset ℕ :=
  ([22953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part022 : ℚ :=
  (11257346265175 : ℚ) / 73729688073801596928

def SurrogateDiagonalTailChunk001Sub000Block156Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22953
    = surrogateDiagTailX0RatChunk001Sub000Block156Part022

theorem surrogateDiagonalTailChunk001Sub000Block156Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part022] using hcert

def TailChunk001Sub000Block156Part023SupportExplicit : Finset ℕ :=
  ([22954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part023 : ℚ :=
  (7649457741025 : ℚ) / 36027568552026066048

def SurrogateDiagonalTailChunk001Sub000Block156Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22954
    = surrogateDiagTailX0RatChunk001Sub000Block156Part023

theorem surrogateDiagonalTailChunk001Sub000Block156Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part023] using hcert

def TailChunk001Sub000Block156Part024SupportExplicit : Finset ℕ :=
  ([22955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block156Part024 : ℚ :=
  (10544054909 : ℚ) / 2273042486156912640

def SurrogateDiagonalTailChunk001Sub000Block156Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22955
    = surrogateDiagTailX0RatChunk001Sub000Block156Part024

theorem surrogateDiagonalTailChunk001Sub000Block156Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block156Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block156Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block156Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block156Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block156Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block156Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block156HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block156Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block156Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block156Part000
    + surrogateDiagTailX0RatChunk001Sub000Block156Part001
    + surrogateDiagTailX0RatChunk001Sub000Block156Part002
    + surrogateDiagTailX0RatChunk001Sub000Block156Part003
    + surrogateDiagTailX0RatChunk001Sub000Block156Part004
    + surrogateDiagTailX0RatChunk001Sub000Block156Part005
    + surrogateDiagTailX0RatChunk001Sub000Block156Part006
    + surrogateDiagTailX0RatChunk001Sub000Block156Part007
    + surrogateDiagTailX0RatChunk001Sub000Block156Part008
    + surrogateDiagTailX0RatChunk001Sub000Block156Part009

def surrogateDiagonalTailChunk001Sub000Block156MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block156Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block156Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block156Part010
    + surrogateDiagTailX0RatChunk001Sub000Block156Part011
    + surrogateDiagTailX0RatChunk001Sub000Block156Part012
    + surrogateDiagTailX0RatChunk001Sub000Block156Part013
    + surrogateDiagTailX0RatChunk001Sub000Block156Part014
    + surrogateDiagTailX0RatChunk001Sub000Block156Part015
    + surrogateDiagTailX0RatChunk001Sub000Block156Part016
    + surrogateDiagTailX0RatChunk001Sub000Block156Part017
    + surrogateDiagTailX0RatChunk001Sub000Block156Part018
    + surrogateDiagTailX0RatChunk001Sub000Block156Part019

def surrogateDiagonalTailChunk001Sub000Block156TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block156Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block156Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block156Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block156Part020
    + surrogateDiagTailX0RatChunk001Sub000Block156Part021
    + surrogateDiagTailX0RatChunk001Sub000Block156Part022
    + surrogateDiagTailX0RatChunk001Sub000Block156Part023
    + surrogateDiagTailX0RatChunk001Sub000Block156Part024

def surrogateDiagonalTailChunk001Sub000Block156Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block156HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block156MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block156TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block156 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block156Part000
    + surrogateDiagTailX0RatChunk001Sub000Block156Part001
    + surrogateDiagTailX0RatChunk001Sub000Block156Part002
    + surrogateDiagTailX0RatChunk001Sub000Block156Part003
    + surrogateDiagTailX0RatChunk001Sub000Block156Part004
    + surrogateDiagTailX0RatChunk001Sub000Block156Part005
    + surrogateDiagTailX0RatChunk001Sub000Block156Part006
    + surrogateDiagTailX0RatChunk001Sub000Block156Part007
    + surrogateDiagTailX0RatChunk001Sub000Block156Part008
    + surrogateDiagTailX0RatChunk001Sub000Block156Part009
    + surrogateDiagTailX0RatChunk001Sub000Block156Part010
    + surrogateDiagTailX0RatChunk001Sub000Block156Part011
    + surrogateDiagTailX0RatChunk001Sub000Block156Part012
    + surrogateDiagTailX0RatChunk001Sub000Block156Part013
    + surrogateDiagTailX0RatChunk001Sub000Block156Part014
    + surrogateDiagTailX0RatChunk001Sub000Block156Part015
    + surrogateDiagTailX0RatChunk001Sub000Block156Part016
    + surrogateDiagTailX0RatChunk001Sub000Block156Part017
    + surrogateDiagTailX0RatChunk001Sub000Block156Part018
    + surrogateDiagTailX0RatChunk001Sub000Block156Part019
    + surrogateDiagTailX0RatChunk001Sub000Block156Part020
    + surrogateDiagTailX0RatChunk001Sub000Block156Part021
    + surrogateDiagTailX0RatChunk001Sub000Block156Part022
    + surrogateDiagTailX0RatChunk001Sub000Block156Part023
    + surrogateDiagTailX0RatChunk001Sub000Block156Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block156_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block156Head + surrogateDiagTailX0RatChunk001Sub000Block156Mid + surrogateDiagTailX0RatChunk001Sub000Block156Tail =
      surrogateDiagTailX0RatChunk001Sub000Block156 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block156Head surrogateDiagTailX0RatChunk001Sub000Block156Mid surrogateDiagTailX0RatChunk001Sub000Block156Tail surrogateDiagTailX0RatChunk001Sub000Block156
  ring

def SurrogateDiagonalTailChunk001Sub000Block156HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block156HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block156Head

def SurrogateDiagonalTailChunk001Sub000Block156MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block156MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block156Mid

def SurrogateDiagonalTailChunk001Sub000Block156TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block156TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block156Tail

theorem surrogateDiagonalTailChunk001Sub000Block156_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block156HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block156MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block156TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block156Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block156 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block156HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block156MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block156TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block156Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block156_eq_head_add_mid_add_tail

/-- Block 157 covers tail-support indices [13925,13950) and q from 22957 to 22998. -/

def TailChunk001Sub000Block157Part000SupportExplicit : Finset ℕ :=
  ([22957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part000 : ℚ :=
  (1367358661 : ℚ) / 1183652129890360200

def SurrogateDiagonalTailChunk001Sub000Block157Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22957
    = surrogateDiagTailX0RatChunk001Sub000Block157Part000

theorem surrogateDiagonalTailChunk001Sub000Block157Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part000] using hcert

def TailChunk001Sub000Block157Part001SupportExplicit : Finset ℕ :=
  ([22958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part001 : ℚ :=
  (27406634875 : ℚ) / 3486451869653501952

def SurrogateDiagonalTailChunk001Sub000Block157Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22958
    = surrogateDiagTailX0RatChunk001Sub000Block157Part001

theorem surrogateDiagonalTailChunk001Sub000Block157Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part001] using hcert

def TailChunk001Sub000Block157Part002SupportExplicit : Finset ℕ :=
  ([22961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22961
    = surrogateDiagTailX0RatChunk001Sub000Block157Part002

theorem surrogateDiagonalTailChunk001Sub000Block157Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part002] using hcert

def TailChunk001Sub000Block157Part003SupportExplicit : Finset ℕ :=
  ([22962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part003 : ℚ :=
  (934763565325 : ℚ) / 7465771467444584448

def SurrogateDiagonalTailChunk001Sub000Block157Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22962
    = surrogateDiagTailX0RatChunk001Sub000Block157Part003

theorem surrogateDiagonalTailChunk001Sub000Block157Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part003] using hcert

def TailChunk001Sub000Block157Part004SupportExplicit : Finset ℕ :=
  ([22963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22963
    = surrogateDiagTailX0RatChunk001Sub000Block157Part004

theorem surrogateDiagonalTailChunk001Sub000Block157Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part004] using hcert

def TailChunk001Sub000Block157Part005SupportExplicit : Finset ℕ :=
  ([22965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part005 : ℚ :=
  (4402566581 : ℚ) / 280622529155174400

def SurrogateDiagonalTailChunk001Sub000Block157Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22965
    = surrogateDiagTailX0RatChunk001Sub000Block157Part005

theorem surrogateDiagonalTailChunk001Sub000Block157Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part005] using hcert

def TailChunk001Sub000Block157Part006SupportExplicit : Finset ℕ :=
  ([22966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22966
    = surrogateDiagTailX0RatChunk001Sub000Block157Part006

theorem surrogateDiagonalTailChunk001Sub000Block157Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part006] using hcert

def TailChunk001Sub000Block157Part007SupportExplicit : Finset ℕ :=
  ([22967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part007 : ℚ :=
  (76618725175 : ℚ) / 24051128563321012224

def SurrogateDiagonalTailChunk001Sub000Block157Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22967
    = surrogateDiagTailX0RatChunk001Sub000Block157Part007

theorem surrogateDiagonalTailChunk001Sub000Block157Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part007] using hcert

def TailChunk001Sub000Block157Part008SupportExplicit : Finset ℕ :=
  ([22969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part008 : ℚ :=
  (2675990125 : ℚ) / 17767966211621311104

def SurrogateDiagonalTailChunk001Sub000Block157Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22969
    = surrogateDiagTailX0RatChunk001Sub000Block157Part008

theorem surrogateDiagonalTailChunk001Sub000Block157Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part008] using hcert

def TailChunk001Sub000Block157Part009SupportExplicit : Finset ℕ :=
  ([22970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part009 : ℚ :=
  (660070645525 : ℚ) / 17789115672644026368

def SurrogateDiagonalTailChunk001Sub000Block157Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22970
    = surrogateDiagTailX0RatChunk001Sub000Block157Part009

theorem surrogateDiagonalTailChunk001Sub000Block157Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part009] using hcert

def TailChunk001Sub000Block157Part010SupportExplicit : Finset ℕ :=
  ([22971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part010 : ℚ :=
  (27293006389 : ℚ) / 2821674129437491200

def SurrogateDiagonalTailChunk001Sub000Block157Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22971
    = surrogateDiagTailX0RatChunk001Sub000Block157Part010

theorem surrogateDiagonalTailChunk001Sub000Block157Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part010] using hcert

def TailChunk001Sub000Block157Part011SupportExplicit : Finset ℕ :=
  ([22973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22973
    = surrogateDiagTailX0RatChunk001Sub000Block157Part011

theorem surrogateDiagonalTailChunk001Sub000Block157Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part011] using hcert

def TailChunk001Sub000Block157Part012SupportExplicit : Finset ℕ :=
  ([22974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part012 : ℚ :=
  (495634898975 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk001Sub000Block157Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22974
    = surrogateDiagTailX0RatChunk001Sub000Block157Part012

theorem surrogateDiagonalTailChunk001Sub000Block157Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part012] using hcert

def TailChunk001Sub000Block157Part013SupportExplicit : Finset ℕ :=
  ([22978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22978
    = surrogateDiagTailX0RatChunk001Sub000Block157Part013

theorem surrogateDiagonalTailChunk001Sub000Block157Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part013] using hcert

def TailChunk001Sub000Block157Part014SupportExplicit : Finset ℕ :=
  ([22979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part014 : ℚ :=
  (1826622517 : ℚ) / 1584264101590425600

def SurrogateDiagonalTailChunk001Sub000Block157Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22979
    = surrogateDiagTailX0RatChunk001Sub000Block157Part014

theorem surrogateDiagonalTailChunk001Sub000Block157Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part014] using hcert

def TailChunk001Sub000Block157Part015SupportExplicit : Finset ℕ :=
  ([22982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22982
    = surrogateDiagTailX0RatChunk001Sub000Block157Part015

theorem surrogateDiagonalTailChunk001Sub000Block157Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part015] using hcert

def TailChunk001Sub000Block157Part016SupportExplicit : Finset ℕ :=
  ([22983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part016 : ℚ :=
  (42864429125 : ℚ) / 41126047398745675776

def SurrogateDiagonalTailChunk001Sub000Block157Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22983
    = surrogateDiagTailX0RatChunk001Sub000Block157Part016

theorem surrogateDiagonalTailChunk001Sub000Block157Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part016] using hcert

def TailChunk001Sub000Block157Part017SupportExplicit : Finset ℕ :=
  ([22985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part017 : ℚ :=
  (1321451612875 : ℚ) / 285618875029435219968

def SurrogateDiagonalTailChunk001Sub000Block157Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22985
    = surrogateDiagTailX0RatChunk001Sub000Block157Part017

theorem surrogateDiagonalTailChunk001Sub000Block157Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part017] using hcert

def TailChunk001Sub000Block157Part018SupportExplicit : Finset ℕ :=
  ([22987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part018 : ℚ :=
  (3816410449 : ℚ) / 26464217128044595200

def SurrogateDiagonalTailChunk001Sub000Block157Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22987
    = surrogateDiagTailX0RatChunk001Sub000Block157Part018

theorem surrogateDiagonalTailChunk001Sub000Block157Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part018] using hcert

def TailChunk001Sub000Block157Part019SupportExplicit : Finset ℕ :=
  ([22989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part019 : ℚ :=
  (53935882475 : ℚ) / 62889796407807442944

def SurrogateDiagonalTailChunk001Sub000Block157Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22989
    = surrogateDiagTailX0RatChunk001Sub000Block157Part019

theorem surrogateDiagonalTailChunk001Sub000Block157Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part019] using hcert

def TailChunk001Sub000Block157Part020SupportExplicit : Finset ℕ :=
  ([22991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part020 : ℚ :=
  (456521775 : ℚ) / 2699680210799958016

def SurrogateDiagonalTailChunk001Sub000Block157Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22991
    = surrogateDiagTailX0RatChunk001Sub000Block157Part020

theorem surrogateDiagonalTailChunk001Sub000Block157Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part020] using hcert

def TailChunk001Sub000Block157Part021SupportExplicit : Finset ℕ :=
  ([22993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22993
    = surrogateDiagTailX0RatChunk001Sub000Block157Part021

theorem surrogateDiagonalTailChunk001Sub000Block157Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part021] using hcert

def TailChunk001Sub000Block157Part022SupportExplicit : Finset ℕ :=
  ([22994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block157Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22994
    = surrogateDiagTailX0RatChunk001Sub000Block157Part022

theorem surrogateDiagonalTailChunk001Sub000Block157Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part022] using hcert

def TailChunk001Sub000Block157Part023SupportExplicit : Finset ℕ :=
  ([22997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part023 : ℚ :=
  (1053530729 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk001Sub000Block157Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22997
    = surrogateDiagTailX0RatChunk001Sub000Block157Part023

theorem surrogateDiagonalTailChunk001Sub000Block157Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part023] using hcert

def TailChunk001Sub000Block157Part024SupportExplicit : Finset ℕ :=
  ([22998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block157Part024 : ℚ :=
  (229597272925 : ℚ) / 2156695597690724352

def SurrogateDiagonalTailChunk001Sub000Block157Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22998
    = surrogateDiagTailX0RatChunk001Sub000Block157Part024

theorem surrogateDiagonalTailChunk001Sub000Block157Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block157Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block157Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block157Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block157Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block157Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block157Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block157HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block157Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block157Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block157Part000
    + surrogateDiagTailX0RatChunk001Sub000Block157Part001
    + surrogateDiagTailX0RatChunk001Sub000Block157Part002
    + surrogateDiagTailX0RatChunk001Sub000Block157Part003
    + surrogateDiagTailX0RatChunk001Sub000Block157Part004
    + surrogateDiagTailX0RatChunk001Sub000Block157Part005
    + surrogateDiagTailX0RatChunk001Sub000Block157Part006
    + surrogateDiagTailX0RatChunk001Sub000Block157Part007
    + surrogateDiagTailX0RatChunk001Sub000Block157Part008
    + surrogateDiagTailX0RatChunk001Sub000Block157Part009

def surrogateDiagonalTailChunk001Sub000Block157MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block157Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block157Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block157Part010
    + surrogateDiagTailX0RatChunk001Sub000Block157Part011
    + surrogateDiagTailX0RatChunk001Sub000Block157Part012
    + surrogateDiagTailX0RatChunk001Sub000Block157Part013
    + surrogateDiagTailX0RatChunk001Sub000Block157Part014
    + surrogateDiagTailX0RatChunk001Sub000Block157Part015
    + surrogateDiagTailX0RatChunk001Sub000Block157Part016
    + surrogateDiagTailX0RatChunk001Sub000Block157Part017
    + surrogateDiagTailX0RatChunk001Sub000Block157Part018
    + surrogateDiagTailX0RatChunk001Sub000Block157Part019

def surrogateDiagonalTailChunk001Sub000Block157TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block157Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block157Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block157Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block157Part020
    + surrogateDiagTailX0RatChunk001Sub000Block157Part021
    + surrogateDiagTailX0RatChunk001Sub000Block157Part022
    + surrogateDiagTailX0RatChunk001Sub000Block157Part023
    + surrogateDiagTailX0RatChunk001Sub000Block157Part024

def surrogateDiagonalTailChunk001Sub000Block157Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block157HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block157MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block157TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block157 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block157Part000
    + surrogateDiagTailX0RatChunk001Sub000Block157Part001
    + surrogateDiagTailX0RatChunk001Sub000Block157Part002
    + surrogateDiagTailX0RatChunk001Sub000Block157Part003
    + surrogateDiagTailX0RatChunk001Sub000Block157Part004
    + surrogateDiagTailX0RatChunk001Sub000Block157Part005
    + surrogateDiagTailX0RatChunk001Sub000Block157Part006
    + surrogateDiagTailX0RatChunk001Sub000Block157Part007
    + surrogateDiagTailX0RatChunk001Sub000Block157Part008
    + surrogateDiagTailX0RatChunk001Sub000Block157Part009
    + surrogateDiagTailX0RatChunk001Sub000Block157Part010
    + surrogateDiagTailX0RatChunk001Sub000Block157Part011
    + surrogateDiagTailX0RatChunk001Sub000Block157Part012
    + surrogateDiagTailX0RatChunk001Sub000Block157Part013
    + surrogateDiagTailX0RatChunk001Sub000Block157Part014
    + surrogateDiagTailX0RatChunk001Sub000Block157Part015
    + surrogateDiagTailX0RatChunk001Sub000Block157Part016
    + surrogateDiagTailX0RatChunk001Sub000Block157Part017
    + surrogateDiagTailX0RatChunk001Sub000Block157Part018
    + surrogateDiagTailX0RatChunk001Sub000Block157Part019
    + surrogateDiagTailX0RatChunk001Sub000Block157Part020
    + surrogateDiagTailX0RatChunk001Sub000Block157Part021
    + surrogateDiagTailX0RatChunk001Sub000Block157Part022
    + surrogateDiagTailX0RatChunk001Sub000Block157Part023
    + surrogateDiagTailX0RatChunk001Sub000Block157Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block157_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block157Head + surrogateDiagTailX0RatChunk001Sub000Block157Mid + surrogateDiagTailX0RatChunk001Sub000Block157Tail =
      surrogateDiagTailX0RatChunk001Sub000Block157 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block157Head surrogateDiagTailX0RatChunk001Sub000Block157Mid surrogateDiagTailX0RatChunk001Sub000Block157Tail surrogateDiagTailX0RatChunk001Sub000Block157
  ring

def SurrogateDiagonalTailChunk001Sub000Block157HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block157HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block157Head

def SurrogateDiagonalTailChunk001Sub000Block157MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block157MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block157Mid

def SurrogateDiagonalTailChunk001Sub000Block157TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block157TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block157Tail

theorem surrogateDiagonalTailChunk001Sub000Block157_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block157HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block157MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block157TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block157Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block157 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block157HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block157MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block157TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block157Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block157_eq_head_add_mid_add_tail

/-- Block 158 covers tail-support indices [13950,13975) and q from 22999 to 23038. -/

def TailChunk001Sub000Block158Part000SupportExplicit : Finset ℕ :=
  ([22999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part000 : ℚ :=
  (3987599473 : ℚ) / 26464217128044595200

def SurrogateDiagonalTailChunk001Sub000Block158Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 22999
    = surrogateDiagTailX0RatChunk001Sub000Block158Part000

theorem surrogateDiagonalTailChunk001Sub000Block158Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part000] using hcert

def TailChunk001Sub000Block158Part001SupportExplicit : Finset ℕ :=
  ([23001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part001 : ℚ :=
  (27360273151 : ℚ) / 2684891430912000000

def SurrogateDiagonalTailChunk001Sub000Block158Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23001
    = surrogateDiagTailX0RatChunk001Sub000Block158Part001

theorem surrogateDiagonalTailChunk001Sub000Block158Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part001] using hcert

def TailChunk001Sub000Block158Part002SupportExplicit : Finset ℕ :=
  ([23002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part002 : ℚ :=
  (542580071 : ℚ) / 17059949112360960

def SurrogateDiagonalTailChunk001Sub000Block158Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23002
    = surrogateDiagTailX0RatChunk001Sub000Block158Part002

theorem surrogateDiagonalTailChunk001Sub000Block158Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part002] using hcert

def TailChunk001Sub000Block158Part003SupportExplicit : Finset ℕ :=
  ([23003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23003
    = surrogateDiagTailX0RatChunk001Sub000Block158Part003

theorem surrogateDiagonalTailChunk001Sub000Block158Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part003] using hcert

def TailChunk001Sub000Block158Part004SupportExplicit : Finset ℕ :=
  ([23005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part004 : ℚ :=
  (708982546175 : ℚ) / 125735366253614874624

def SurrogateDiagonalTailChunk001Sub000Block158Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23005
    = surrogateDiagTailX0RatChunk001Sub000Block158Part004

theorem surrogateDiagonalTailChunk001Sub000Block158Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part004] using hcert

def TailChunk001Sub000Block158Part005SupportExplicit : Finset ℕ :=
  ([23006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23006
    = surrogateDiagTailX0RatChunk001Sub000Block158Part005

theorem surrogateDiagonalTailChunk001Sub000Block158Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part005] using hcert

def TailChunk001Sub000Block158Part006SupportExplicit : Finset ℕ :=
  ([23007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part006 : ℚ :=
  (41675 : ℚ) / 9219283054811136

def SurrogateDiagonalTailChunk001Sub000Block158Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23007
    = surrogateDiagTailX0RatChunk001Sub000Block158Part006

theorem surrogateDiagonalTailChunk001Sub000Block158Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part006] using hcert

def TailChunk001Sub000Block158Part007SupportExplicit : Finset ℕ :=
  ([23009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part007 : ℚ :=
  (1007692174525 : ℚ) / 297738960968982233088

def SurrogateDiagonalTailChunk001Sub000Block158Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23009
    = surrogateDiagTailX0RatChunk001Sub000Block158Part007

theorem surrogateDiagonalTailChunk001Sub000Block158Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part007] using hcert

def TailChunk001Sub000Block158Part008SupportExplicit : Finset ℕ :=
  ([23010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part008 : ℚ :=
  (169653746725 : ℚ) / 400564553093480448

def SurrogateDiagonalTailChunk001Sub000Block158Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23010
    = surrogateDiagTailX0RatChunk001Sub000Block158Part008

theorem surrogateDiagonalTailChunk001Sub000Block158Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part008] using hcert

def TailChunk001Sub000Block158Part009SupportExplicit : Finset ℕ :=
  ([23011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23011
    = surrogateDiagTailX0RatChunk001Sub000Block158Part009

theorem surrogateDiagonalTailChunk001Sub000Block158Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part009] using hcert

def TailChunk001Sub000Block158Part010SupportExplicit : Finset ℕ :=
  ([23014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part010 : ℚ :=
  (27626021 : ℚ) / 10009489548810240

def SurrogateDiagonalTailChunk001Sub000Block158Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23014
    = surrogateDiagTailX0RatChunk001Sub000Block158Part010

theorem surrogateDiagonalTailChunk001Sub000Block158Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part010] using hcert

def TailChunk001Sub000Block158Part011SupportExplicit : Finset ℕ :=
  ([23015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part011 : ℚ :=
  (1324900862125 : ℚ) / 287113280605704603648

def SurrogateDiagonalTailChunk001Sub000Block158Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23015
    = surrogateDiagTailX0RatChunk001Sub000Block158Part011

theorem surrogateDiagonalTailChunk001Sub000Block158Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part011] using hcert

def TailChunk001Sub000Block158Part012SupportExplicit : Finset ℕ :=
  ([23017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23017
    = surrogateDiagTailX0RatChunk001Sub000Block158Part012

theorem surrogateDiagonalTailChunk001Sub000Block158Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part012] using hcert

def TailChunk001Sub000Block158Part013SupportExplicit : Finset ℕ :=
  ([23018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part013 : ℚ :=
  (102342681875 : ℚ) / 17110534552691933184

def SurrogateDiagonalTailChunk001Sub000Block158Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23018
    = surrogateDiagTailX0RatChunk001Sub000Block158Part013

theorem surrogateDiagonalTailChunk001Sub000Block158Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part013] using hcert

def TailChunk001Sub000Block158Part014SupportExplicit : Finset ℕ :=
  ([23019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part014 : ℚ :=
  (125025 : ℚ) / 27715605029224448

def SurrogateDiagonalTailChunk001Sub000Block158Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23019
    = surrogateDiagTailX0RatChunk001Sub000Block158Part014

theorem surrogateDiagonalTailChunk001Sub000Block158Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part014] using hcert

def TailChunk001Sub000Block158Part015SupportExplicit : Finset ℕ :=
  ([23021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23021
    = surrogateDiagTailX0RatChunk001Sub000Block158Part015

theorem surrogateDiagonalTailChunk001Sub000Block158Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part015] using hcert

def TailChunk001Sub000Block158Part016SupportExplicit : Finset ℕ :=
  ([23023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part016 : ℚ :=
  (1764218383 : ℚ) / 174906141209395200

def SurrogateDiagonalTailChunk001Sub000Block158Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23023
    = surrogateDiagTailX0RatChunk001Sub000Block158Part016

theorem surrogateDiagonalTailChunk001Sub000Block158Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part016] using hcert

def TailChunk001Sub000Block158Part017SupportExplicit : Finset ℕ :=
  ([23026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part017 : ℚ :=
  (5659914775 : ℚ) / 1574811168914092032

def SurrogateDiagonalTailChunk001Sub000Block158Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23026
    = surrogateDiagTailX0RatChunk001Sub000Block158Part017

theorem surrogateDiagonalTailChunk001Sub000Block158Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part017] using hcert

def TailChunk001Sub000Block158Part018SupportExplicit : Finset ℕ :=
  ([23027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23027
    = surrogateDiagTailX0RatChunk001Sub000Block158Part018

theorem surrogateDiagonalTailChunk001Sub000Block158Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part018] using hcert

def TailChunk001Sub000Block158Part019SupportExplicit : Finset ℕ :=
  ([23029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23029
    = surrogateDiagTailX0RatChunk001Sub000Block158Part019

theorem surrogateDiagonalTailChunk001Sub000Block158Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part019] using hcert

def TailChunk001Sub000Block158Part020SupportExplicit : Finset ℕ :=
  ([23033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part020 : ℚ :=
  (14282473 : ℚ) / 35082412459155936

def SurrogateDiagonalTailChunk001Sub000Block158Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23033
    = surrogateDiagTailX0RatChunk001Sub000Block158Part020

theorem surrogateDiagonalTailChunk001Sub000Block158Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part020] using hcert

def TailChunk001Sub000Block158Part021SupportExplicit : Finset ℕ :=
  ([23034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part021 : ℚ :=
  (39002422387 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk001Sub000Block158Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23034
    = surrogateDiagTailX0RatChunk001Sub000Block158Part021

theorem surrogateDiagonalTailChunk001Sub000Block158Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part021] using hcert

def TailChunk001Sub000Block158Part022SupportExplicit : Finset ℕ :=
  ([23035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part022 : ℚ :=
  (6528984683 : ℚ) / 990875963149516800

def SurrogateDiagonalTailChunk001Sub000Block158Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23035
    = surrogateDiagTailX0RatChunk001Sub000Block158Part022

theorem surrogateDiagonalTailChunk001Sub000Block158Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part022] using hcert

def TailChunk001Sub000Block158Part023SupportExplicit : Finset ℕ :=
  ([23037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part023 : ℚ :=
  (829735061725 : ℚ) / 74815926702828945408

def SurrogateDiagonalTailChunk001Sub000Block158Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23037
    = surrogateDiagTailX0RatChunk001Sub000Block158Part023

theorem surrogateDiagonalTailChunk001Sub000Block158Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part023] using hcert

def TailChunk001Sub000Block158Part024SupportExplicit : Finset ℕ :=
  ([23038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block158Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block158Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23038
    = surrogateDiagTailX0RatChunk001Sub000Block158Part024

theorem surrogateDiagonalTailChunk001Sub000Block158Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block158Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block158Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block158Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block158Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block158Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block158Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block158HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block158Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block158Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block158Part000
    + surrogateDiagTailX0RatChunk001Sub000Block158Part001
    + surrogateDiagTailX0RatChunk001Sub000Block158Part002
    + surrogateDiagTailX0RatChunk001Sub000Block158Part003
    + surrogateDiagTailX0RatChunk001Sub000Block158Part004
    + surrogateDiagTailX0RatChunk001Sub000Block158Part005
    + surrogateDiagTailX0RatChunk001Sub000Block158Part006
    + surrogateDiagTailX0RatChunk001Sub000Block158Part007
    + surrogateDiagTailX0RatChunk001Sub000Block158Part008
    + surrogateDiagTailX0RatChunk001Sub000Block158Part009

def surrogateDiagonalTailChunk001Sub000Block158MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block158Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block158Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block158Part010
    + surrogateDiagTailX0RatChunk001Sub000Block158Part011
    + surrogateDiagTailX0RatChunk001Sub000Block158Part012
    + surrogateDiagTailX0RatChunk001Sub000Block158Part013
    + surrogateDiagTailX0RatChunk001Sub000Block158Part014
    + surrogateDiagTailX0RatChunk001Sub000Block158Part015
    + surrogateDiagTailX0RatChunk001Sub000Block158Part016
    + surrogateDiagTailX0RatChunk001Sub000Block158Part017
    + surrogateDiagTailX0RatChunk001Sub000Block158Part018
    + surrogateDiagTailX0RatChunk001Sub000Block158Part019

def surrogateDiagonalTailChunk001Sub000Block158TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block158Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block158Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block158Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block158Part020
    + surrogateDiagTailX0RatChunk001Sub000Block158Part021
    + surrogateDiagTailX0RatChunk001Sub000Block158Part022
    + surrogateDiagTailX0RatChunk001Sub000Block158Part023
    + surrogateDiagTailX0RatChunk001Sub000Block158Part024

def surrogateDiagonalTailChunk001Sub000Block158Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block158HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block158MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block158TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block158 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block158Part000
    + surrogateDiagTailX0RatChunk001Sub000Block158Part001
    + surrogateDiagTailX0RatChunk001Sub000Block158Part002
    + surrogateDiagTailX0RatChunk001Sub000Block158Part003
    + surrogateDiagTailX0RatChunk001Sub000Block158Part004
    + surrogateDiagTailX0RatChunk001Sub000Block158Part005
    + surrogateDiagTailX0RatChunk001Sub000Block158Part006
    + surrogateDiagTailX0RatChunk001Sub000Block158Part007
    + surrogateDiagTailX0RatChunk001Sub000Block158Part008
    + surrogateDiagTailX0RatChunk001Sub000Block158Part009
    + surrogateDiagTailX0RatChunk001Sub000Block158Part010
    + surrogateDiagTailX0RatChunk001Sub000Block158Part011
    + surrogateDiagTailX0RatChunk001Sub000Block158Part012
    + surrogateDiagTailX0RatChunk001Sub000Block158Part013
    + surrogateDiagTailX0RatChunk001Sub000Block158Part014
    + surrogateDiagTailX0RatChunk001Sub000Block158Part015
    + surrogateDiagTailX0RatChunk001Sub000Block158Part016
    + surrogateDiagTailX0RatChunk001Sub000Block158Part017
    + surrogateDiagTailX0RatChunk001Sub000Block158Part018
    + surrogateDiagTailX0RatChunk001Sub000Block158Part019
    + surrogateDiagTailX0RatChunk001Sub000Block158Part020
    + surrogateDiagTailX0RatChunk001Sub000Block158Part021
    + surrogateDiagTailX0RatChunk001Sub000Block158Part022
    + surrogateDiagTailX0RatChunk001Sub000Block158Part023
    + surrogateDiagTailX0RatChunk001Sub000Block158Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block158_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block158Head + surrogateDiagTailX0RatChunk001Sub000Block158Mid + surrogateDiagTailX0RatChunk001Sub000Block158Tail =
      surrogateDiagTailX0RatChunk001Sub000Block158 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block158Head surrogateDiagTailX0RatChunk001Sub000Block158Mid surrogateDiagTailX0RatChunk001Sub000Block158Tail surrogateDiagTailX0RatChunk001Sub000Block158
  ring

def SurrogateDiagonalTailChunk001Sub000Block158HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block158HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block158Head

def SurrogateDiagonalTailChunk001Sub000Block158MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block158MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block158Mid

def SurrogateDiagonalTailChunk001Sub000Block158TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block158TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block158Tail

theorem surrogateDiagonalTailChunk001Sub000Block158_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block158HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block158MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block158TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block158Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block158 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block158HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block158MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block158TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block158Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block158_eq_head_add_mid_add_tail

/-- Block 159 covers tail-support indices [13975,14000) and q from 23039 to 23078. -/

def TailChunk001Sub000Block159Part000SupportExplicit : Finset ℕ :=
  ([23039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23039
    = surrogateDiagTailX0RatChunk001Sub000Block159Part000

theorem surrogateDiagonalTailChunk001Sub000Block159Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part000] using hcert

def TailChunk001Sub000Block159Part001SupportExplicit : Finset ℕ :=
  ([23041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23041
    = surrogateDiagTailX0RatChunk001Sub000Block159Part001

theorem surrogateDiagonalTailChunk001Sub000Block159Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part001] using hcert

def TailChunk001Sub000Block159Part002SupportExplicit : Finset ℕ :=
  ([23042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part002 : ℚ :=
  (401616139 : ℚ) / 157383406387200000

def SurrogateDiagonalTailChunk001Sub000Block159Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23042
    = surrogateDiagTailX0RatChunk001Sub000Block159Part002

theorem surrogateDiagonalTailChunk001Sub000Block159Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part002] using hcert

def TailChunk001Sub000Block159Part003SupportExplicit : Finset ℕ :=
  ([23043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part003 : ℚ :=
  (1667 : ℚ) / 371085174374400

def SurrogateDiagonalTailChunk001Sub000Block159Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23043
    = surrogateDiagTailX0RatChunk001Sub000Block159Part003

theorem surrogateDiagonalTailChunk001Sub000Block159Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part003] using hcert

def TailChunk001Sub000Block159Part004SupportExplicit : Finset ℕ :=
  ([23045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part004 : ℚ :=
  (2287966899 : ℚ) / 260561765301207040

def SurrogateDiagonalTailChunk001Sub000Block159Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23045
    = surrogateDiagTailX0RatChunk001Sub000Block159Part004

theorem surrogateDiagonalTailChunk001Sub000Block159Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part004] using hcert

def TailChunk001Sub000Block159Part005SupportExplicit : Finset ℕ :=
  ([23046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part005 : ℚ :=
  (941992037875 : ℚ) / 7116556751017494528

def SurrogateDiagonalTailChunk001Sub000Block159Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23046
    = surrogateDiagTailX0RatChunk001Sub000Block159Part005

theorem surrogateDiagonalTailChunk001Sub000Block159Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part005] using hcert

def TailChunk001Sub000Block159Part006SupportExplicit : Finset ℕ :=
  ([23047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part006 : ℚ :=
  (41404267525 : ℚ) / 62933929484008753152

def SurrogateDiagonalTailChunk001Sub000Block159Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23047
    = surrogateDiagTailX0RatChunk001Sub000Block159Part006

theorem surrogateDiagonalTailChunk001Sub000Block159Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part006] using hcert

def TailChunk001Sub000Block159Part007SupportExplicit : Finset ℕ :=
  ([23051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part007 : ℚ :=
  (247148325575 : ℚ) / 54402806161770283008

def SurrogateDiagonalTailChunk001Sub000Block159Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23051
    = surrogateDiagTailX0RatChunk001Sub000Block159Part007

theorem surrogateDiagonalTailChunk001Sub000Block159Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part007] using hcert

def TailChunk001Sub000Block159Part008SupportExplicit : Finset ℕ :=
  ([23053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23053
    = surrogateDiagTailX0RatChunk001Sub000Block159Part008

theorem surrogateDiagonalTailChunk001Sub000Block159Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part008] using hcert

def TailChunk001Sub000Block159Part009SupportExplicit : Finset ℕ :=
  ([23054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23054
    = surrogateDiagTailX0RatChunk001Sub000Block159Part009

theorem surrogateDiagonalTailChunk001Sub000Block159Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part009] using hcert

def TailChunk001Sub000Block159Part010SupportExplicit : Finset ℕ :=
  ([23055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part010 : ℚ :=
  (497981622575 : ℚ) / 23014540645503074304

def SurrogateDiagonalTailChunk001Sub000Block159Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23055
    = surrogateDiagTailX0RatChunk001Sub000Block159Part010

theorem surrogateDiagonalTailChunk001Sub000Block159Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part010] using hcert

def TailChunk001Sub000Block159Part011SupportExplicit : Finset ℕ :=
  ([23057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23057
    = surrogateDiagTailX0RatChunk001Sub000Block159Part011

theorem surrogateDiagonalTailChunk001Sub000Block159Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part011] using hcert

def TailChunk001Sub000Block159Part012SupportExplicit : Finset ℕ :=
  ([23059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23059
    = surrogateDiagTailX0RatChunk001Sub000Block159Part012

theorem surrogateDiagonalTailChunk001Sub000Block159Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part012] using hcert

def TailChunk001Sub000Block159Part013SupportExplicit : Finset ℕ :=
  ([23061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part013 : ℚ :=
  (41675 : ℚ) / 9306154380168576

def SurrogateDiagonalTailChunk001Sub000Block159Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23061
    = surrogateDiagTailX0RatChunk001Sub000Block159Part013

theorem surrogateDiagonalTailChunk001Sub000Block159Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part013] using hcert

def TailChunk001Sub000Block159Part014SupportExplicit : Finset ℕ :=
  ([23062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part014 : ℚ :=
  (297831671875 : ℚ) / 31951167401318565888

def SurrogateDiagonalTailChunk001Sub000Block159Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23062
    = surrogateDiagTailX0RatChunk001Sub000Block159Part014

theorem surrogateDiagonalTailChunk001Sub000Block159Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part014] using hcert

def TailChunk001Sub000Block159Part015SupportExplicit : Finset ℕ :=
  ([23063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23063
    = surrogateDiagTailX0RatChunk001Sub000Block159Part015

theorem surrogateDiagonalTailChunk001Sub000Block159Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part015] using hcert

def TailChunk001Sub000Block159Part016SupportExplicit : Finset ℕ :=
  ([23065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part016 : ℚ :=
  (55079310425 : ℚ) / 4319892100478803968

def SurrogateDiagonalTailChunk001Sub000Block159Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23065
    = surrogateDiagTailX0RatChunk001Sub000Block159Part016

theorem surrogateDiagonalTailChunk001Sub000Block159Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part016] using hcert

def TailChunk001Sub000Block159Part017SupportExplicit : Finset ℕ :=
  ([23066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part017 : ℚ :=
  (188982949075 : ℚ) / 35400335334754923648

def SurrogateDiagonalTailChunk001Sub000Block159Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23066
    = surrogateDiagTailX0RatChunk001Sub000Block159Part017

theorem surrogateDiagonalTailChunk001Sub000Block159Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part017] using hcert

def TailChunk001Sub000Block159Part018SupportExplicit : Finset ℕ :=
  ([23069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part018 : ℚ :=
  (267779034975 : ℚ) / 144806558563991289856

def SurrogateDiagonalTailChunk001Sub000Block159Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23069
    = surrogateDiagTailX0RatChunk001Sub000Block159Part018

theorem surrogateDiagonalTailChunk001Sub000Block159Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part018] using hcert

def TailChunk001Sub000Block159Part019SupportExplicit : Finset ℕ :=
  ([23070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part019 : ℚ :=
  (997842162475 : ℚ) / 3563130157529038848

def SurrogateDiagonalTailChunk001Sub000Block159Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23070
    = surrogateDiagTailX0RatChunk001Sub000Block159Part019

theorem surrogateDiagonalTailChunk001Sub000Block159Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part019] using hcert

def TailChunk001Sub000Block159Part020SupportExplicit : Finset ℕ :=
  ([23071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block159Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23071
    = surrogateDiagTailX0RatChunk001Sub000Block159Part020

theorem surrogateDiagonalTailChunk001Sub000Block159Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part020] using hcert

def TailChunk001Sub000Block159Part021SupportExplicit : Finset ℕ :=
  ([23073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part021 : ℚ :=
  (5001 : ℚ) / 1119065063427200

def SurrogateDiagonalTailChunk001Sub000Block159Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23073
    = surrogateDiagTailX0RatChunk001Sub000Block159Part021

theorem surrogateDiagonalTailChunk001Sub000Block159Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part021] using hcert

def TailChunk001Sub000Block159Part022SupportExplicit : Finset ℕ :=
  ([23074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part022 : ℚ :=
  (1281125 : ℚ) / 771631157812488

def SurrogateDiagonalTailChunk001Sub000Block159Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23074
    = surrogateDiagTailX0RatChunk001Sub000Block159Part022

theorem surrogateDiagonalTailChunk001Sub000Block159Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part022] using hcert

def TailChunk001Sub000Block159Part023SupportExplicit : Finset ℕ :=
  ([23077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part023 : ℚ :=
  (131296133 : ℚ) / 516336103096425024

def SurrogateDiagonalTailChunk001Sub000Block159Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23077
    = surrogateDiagTailX0RatChunk001Sub000Block159Part023

theorem surrogateDiagonalTailChunk001Sub000Block159Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part023] using hcert

def TailChunk001Sub000Block159Part024SupportExplicit : Finset ℕ :=
  ([23078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block159Part024 : ℚ :=
  (21629527 : ℚ) / 1885176454298880

def SurrogateDiagonalTailChunk001Sub000Block159Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23078
    = surrogateDiagTailX0RatChunk001Sub000Block159Part024

theorem surrogateDiagonalTailChunk001Sub000Block159Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block159Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block159Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block159Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block159Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block159Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block159Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block159HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block159Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block159Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block159Part000
    + surrogateDiagTailX0RatChunk001Sub000Block159Part001
    + surrogateDiagTailX0RatChunk001Sub000Block159Part002
    + surrogateDiagTailX0RatChunk001Sub000Block159Part003
    + surrogateDiagTailX0RatChunk001Sub000Block159Part004
    + surrogateDiagTailX0RatChunk001Sub000Block159Part005
    + surrogateDiagTailX0RatChunk001Sub000Block159Part006
    + surrogateDiagTailX0RatChunk001Sub000Block159Part007
    + surrogateDiagTailX0RatChunk001Sub000Block159Part008
    + surrogateDiagTailX0RatChunk001Sub000Block159Part009

def surrogateDiagonalTailChunk001Sub000Block159MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block159Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block159Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block159Part010
    + surrogateDiagTailX0RatChunk001Sub000Block159Part011
    + surrogateDiagTailX0RatChunk001Sub000Block159Part012
    + surrogateDiagTailX0RatChunk001Sub000Block159Part013
    + surrogateDiagTailX0RatChunk001Sub000Block159Part014
    + surrogateDiagTailX0RatChunk001Sub000Block159Part015
    + surrogateDiagTailX0RatChunk001Sub000Block159Part016
    + surrogateDiagTailX0RatChunk001Sub000Block159Part017
    + surrogateDiagTailX0RatChunk001Sub000Block159Part018
    + surrogateDiagTailX0RatChunk001Sub000Block159Part019

def surrogateDiagonalTailChunk001Sub000Block159TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block159Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block159Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block159Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block159Part020
    + surrogateDiagTailX0RatChunk001Sub000Block159Part021
    + surrogateDiagTailX0RatChunk001Sub000Block159Part022
    + surrogateDiagTailX0RatChunk001Sub000Block159Part023
    + surrogateDiagTailX0RatChunk001Sub000Block159Part024

def surrogateDiagonalTailChunk001Sub000Block159Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block159HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block159MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block159TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block159 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block159Part000
    + surrogateDiagTailX0RatChunk001Sub000Block159Part001
    + surrogateDiagTailX0RatChunk001Sub000Block159Part002
    + surrogateDiagTailX0RatChunk001Sub000Block159Part003
    + surrogateDiagTailX0RatChunk001Sub000Block159Part004
    + surrogateDiagTailX0RatChunk001Sub000Block159Part005
    + surrogateDiagTailX0RatChunk001Sub000Block159Part006
    + surrogateDiagTailX0RatChunk001Sub000Block159Part007
    + surrogateDiagTailX0RatChunk001Sub000Block159Part008
    + surrogateDiagTailX0RatChunk001Sub000Block159Part009
    + surrogateDiagTailX0RatChunk001Sub000Block159Part010
    + surrogateDiagTailX0RatChunk001Sub000Block159Part011
    + surrogateDiagTailX0RatChunk001Sub000Block159Part012
    + surrogateDiagTailX0RatChunk001Sub000Block159Part013
    + surrogateDiagTailX0RatChunk001Sub000Block159Part014
    + surrogateDiagTailX0RatChunk001Sub000Block159Part015
    + surrogateDiagTailX0RatChunk001Sub000Block159Part016
    + surrogateDiagTailX0RatChunk001Sub000Block159Part017
    + surrogateDiagTailX0RatChunk001Sub000Block159Part018
    + surrogateDiagTailX0RatChunk001Sub000Block159Part019
    + surrogateDiagTailX0RatChunk001Sub000Block159Part020
    + surrogateDiagTailX0RatChunk001Sub000Block159Part021
    + surrogateDiagTailX0RatChunk001Sub000Block159Part022
    + surrogateDiagTailX0RatChunk001Sub000Block159Part023
    + surrogateDiagTailX0RatChunk001Sub000Block159Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block159_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block159Head + surrogateDiagTailX0RatChunk001Sub000Block159Mid + surrogateDiagTailX0RatChunk001Sub000Block159Tail =
      surrogateDiagTailX0RatChunk001Sub000Block159 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block159Head surrogateDiagTailX0RatChunk001Sub000Block159Mid surrogateDiagTailX0RatChunk001Sub000Block159Tail surrogateDiagTailX0RatChunk001Sub000Block159
  ring

def SurrogateDiagonalTailChunk001Sub000Block159HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block159HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block159Head

def SurrogateDiagonalTailChunk001Sub000Block159MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block159MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block159Mid

def SurrogateDiagonalTailChunk001Sub000Block159TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block159TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block159Tail

theorem surrogateDiagonalTailChunk001Sub000Block159_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block159HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block159MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block159TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block159Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block159 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block159HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block159MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block159TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block159Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block159_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
