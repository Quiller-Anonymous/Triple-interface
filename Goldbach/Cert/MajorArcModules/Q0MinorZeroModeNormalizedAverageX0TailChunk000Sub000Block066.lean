import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [66,67). -/

/- Block 066 covers tail-support indices [1650,1675) and q from 2765 to 2805. -/

def TailChunk000Sub000Block066Part000SupportExplicit : Finset ℕ :=
  ([2765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part000 : ℚ :=
  (624672364075 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block066Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2765
    = surrogateDiagTailX0RatChunk000Sub000Block066Part000

theorem surrogateDiagonalTailChunk000Sub000Block066Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part000] using hcert

def TailChunk000Sub000Block066Part001SupportExplicit : Finset ℕ :=
  ([2766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part001 : ℚ :=
  (12194279629 : ℚ) / 71653623859200

def SurrogateDiagonalTailChunk000Sub000Block066Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2766
    = surrogateDiagTailX0RatChunk000Sub000Block066Part001

theorem surrogateDiagonalTailChunk000Sub000Block066Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part001] using hcert

def TailChunk000Sub000Block066Part002SupportExplicit : Finset ℕ :=
  ([2767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part002 : ℚ :=
  (956844717775 : ℚ) / 146364435462525768

def SurrogateDiagonalTailChunk000Sub000Block066Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2767
    = surrogateDiagTailX0RatChunk000Sub000Block066Part002

theorem surrogateDiagonalTailChunk000Sub000Block066Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part002] using hcert

def TailChunk000Sub000Block066Part003SupportExplicit : Finset ℕ :=
  ([2769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part003 : ℚ :=
  (7674545093 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk000Sub000Block066Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2769
    = surrogateDiagTailX0RatChunk000Sub000Block066Part003

theorem surrogateDiagonalTailChunk000Sub000Block066Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part003] using hcert

def TailChunk000Sub000Block066Part004SupportExplicit : Finset ℕ :=
  ([2770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part004 : ℚ :=
  (18827599075 : ℚ) / 232157741303808

def SurrogateDiagonalTailChunk000Sub000Block066Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2770
    = surrogateDiagTailX0RatChunk000Sub000Block066Part004

theorem surrogateDiagonalTailChunk000Sub000Block066Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part004] using hcert

def TailChunk000Sub000Block066Part005SupportExplicit : Finset ℕ :=
  ([2771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part005 : ℚ :=
  (297505022375 : ℚ) / 37622321725833216

def SurrogateDiagonalTailChunk000Sub000Block066Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2771
    = surrogateDiagTailX0RatChunk000Sub000Block066Part005

theorem surrogateDiagonalTailChunk000Sub000Block066Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part005] using hcert

def TailChunk000Sub000Block066Part006SupportExplicit : Finset ℕ :=
  ([2773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part006 : ℚ :=
  (460731987725 : ℚ) / 63349058420948544

def SurrogateDiagonalTailChunk000Sub000Block066Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2773
    = surrogateDiagTailX0RatChunk000Sub000Block066Part006

theorem surrogateDiagonalTailChunk000Sub000Block066Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part006] using hcert

def TailChunk000Sub000Block066Part007SupportExplicit : Finset ℕ :=
  ([2774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part007 : ℚ :=
  (49584643175 : ℚ) / 783798369288192

def SurrogateDiagonalTailChunk000Sub000Block066Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2774
    = surrogateDiagTailX0RatChunk000Sub000Block066Part007

theorem surrogateDiagonalTailChunk000Sub000Block066Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part007] using hcert

def TailChunk000Sub000Block066Part008SupportExplicit : Finset ℕ :=
  ([2777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part008 : ℚ :=
  (120495765625 : ℚ) / 37123140982927872

def SurrogateDiagonalTailChunk000Sub000Block066Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2777
    = surrogateDiagTailX0RatChunk000Sub000Block066Part008

theorem surrogateDiagonalTailChunk000Sub000Block066Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part008] using hcert

def TailChunk000Sub000Block066Part009SupportExplicit : Finset ℕ :=
  ([2778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part009 : ℚ :=
  (307508247775 : ℚ) / 1822698112169088

def SurrogateDiagonalTailChunk000Sub000Block066Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2778
    = surrogateDiagTailX0RatChunk000Sub000Block066Part009

theorem surrogateDiagonalTailChunk000Sub000Block066Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part009] using hcert

def TailChunk000Sub000Block066Part010SupportExplicit : Finset ℕ :=
  ([2779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part010 : ℚ :=
  (407756660225 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block066Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2779
    = surrogateDiagTailX0RatChunk000Sub000Block066Part010

theorem surrogateDiagonalTailChunk000Sub000Block066Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part010] using hcert

def TailChunk000Sub000Block066Part011SupportExplicit : Finset ℕ :=
  ([2782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part011 : ℚ :=
  (36540976625 : ℚ) / 545499124729344

def SurrogateDiagonalTailChunk000Sub000Block066Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2782
    = surrogateDiagTailX0RatChunk000Sub000Block066Part011

theorem surrogateDiagonalTailChunk000Sub000Block066Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part011] using hcert

def TailChunk000Sub000Block066Part012SupportExplicit : Finset ℕ :=
  ([2785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part012 : ℚ :=
  (94364336675 : ℚ) / 7646734360743936

def SurrogateDiagonalTailChunk000Sub000Block066Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2785
    = surrogateDiagTailX0RatChunk000Sub000Block066Part012

theorem surrogateDiagonalTailChunk000Sub000Block066Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part012] using hcert

def TailChunk000Sub000Block066Part013SupportExplicit : Finset ℕ :=
  ([2786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part013 : ℚ :=
  (45136900675 : ℚ) / 553413962420352

def SurrogateDiagonalTailChunk000Sub000Block066Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2786
    = surrogateDiagTailX0RatChunk000Sub000Block066Part013

theorem surrogateDiagonalTailChunk000Sub000Block066Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part013] using hcert

def TailChunk000Sub000Block066Part014SupportExplicit : Finset ℕ :=
  ([2787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part014 : ℚ :=
  (592796187175 : ℚ) / 29671448377294848

def SurrogateDiagonalTailChunk000Sub000Block066Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2787
    = surrogateDiagTailX0RatChunk000Sub000Block066Part014

theorem surrogateDiagonalTailChunk000Sub000Block066Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part014] using hcert

def TailChunk000Sub000Block066Part015SupportExplicit : Finset ℕ :=
  ([2789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part015 : ℚ :=
  (972120661975 : ℚ) / 151076855397053568

def SurrogateDiagonalTailChunk000Sub000Block066Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2789
    = surrogateDiagTailX0RatChunk000Sub000Block066Part015

theorem surrogateDiagonalTailChunk000Sub000Block066Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part015] using hcert

def TailChunk000Sub000Block066Part016SupportExplicit : Finset ℕ :=
  ([2791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part016 : ℚ :=
  (194742025 : ℚ) / 60604331252562

def SurrogateDiagonalTailChunk000Sub000Block066Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2791
    = surrogateDiagTailX0RatChunk000Sub000Block066Part016

theorem surrogateDiagonalTailChunk000Sub000Block066Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part016] using hcert

def TailChunk000Sub000Block066Part017SupportExplicit : Finset ℕ :=
  ([2794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part017 : ℚ :=
  (3478491251 : ℚ) / 50419557095040

def SurrogateDiagonalTailChunk000Sub000Block066Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2794
    = surrogateDiagTailX0RatChunk000Sub000Block066Part017

theorem surrogateDiagonalTailChunk000Sub000Block066Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part017] using hcert

def TailChunk000Sub000Block066Part018SupportExplicit : Finset ℕ :=
  ([2795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part018 : ℚ :=
  (170141971225 : ℚ) / 10325925293064192

def SurrogateDiagonalTailChunk000Sub000Block066Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2795
    = surrogateDiagTailX0RatChunk000Sub000Block066Part018

theorem surrogateDiagonalTailChunk000Sub000Block066Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part018] using hcert

def TailChunk000Sub000Block066Part019SupportExplicit : Finset ℕ :=
  ([2797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part019 : ℚ :=
  (977705544775 : ℚ) / 152818357368601728

def SurrogateDiagonalTailChunk000Sub000Block066Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2797
    = surrogateDiagTailX0RatChunk000Sub000Block066Part019

theorem surrogateDiagonalTailChunk000Sub000Block066Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part019] using hcert

def TailChunk000Sub000Block066Part020SupportExplicit : Finset ℕ :=
  ([2798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part020 : ℚ :=
  (40758710825 : ℚ) / 1061238592837512

def SurrogateDiagonalTailChunk000Sub000Block066Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2798
    = surrogateDiagTailX0RatChunk000Sub000Block066Part020

theorem surrogateDiagonalTailChunk000Sub000Block066Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part020] using hcert

def TailChunk000Sub000Block066Part021SupportExplicit : Finset ℕ :=
  ([2801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part021 : ℚ :=
  (39220159399 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk000Sub000Block066Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2801
    = surrogateDiagTailX0RatChunk000Sub000Block066Part021

theorem surrogateDiagonalTailChunk000Sub000Block066Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part021] using hcert

def TailChunk000Sub000Block066Part022SupportExplicit : Finset ℕ :=
  ([2802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part022 : ℚ :=
  (312845268475 : ℚ) / 1886646387266688

def SurrogateDiagonalTailChunk000Sub000Block066Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2802
    = surrogateDiagTailX0RatChunk000Sub000Block066Part022

theorem surrogateDiagonalTailChunk000Sub000Block066Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part022] using hcert

def TailChunk000Sub000Block066Part023SupportExplicit : Finset ℕ :=
  ([2803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part023 : ℚ :=
  (981904704775 : ℚ) / 154134331326164808

def SurrogateDiagonalTailChunk000Sub000Block066Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2803
    = surrogateDiagTailX0RatChunk000Sub000Block066Part023

theorem surrogateDiagonalTailChunk000Sub000Block066Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part023] using hcert

def TailChunk000Sub000Block066Part024SupportExplicit : Finset ℕ :=
  ([2805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block066Part024 : ℚ :=
  (1728200779 : ℚ) / 26848914309120

def SurrogateDiagonalTailChunk000Sub000Block066Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2805
    = surrogateDiagTailX0RatChunk000Sub000Block066Part024

theorem surrogateDiagonalTailChunk000Sub000Block066Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block066Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block066Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block066Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block066Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block066Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block066HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block066Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block066Part000
    + surrogateDiagTailX0RatChunk000Sub000Block066Part001
    + surrogateDiagTailX0RatChunk000Sub000Block066Part002
    + surrogateDiagTailX0RatChunk000Sub000Block066Part003
    + surrogateDiagTailX0RatChunk000Sub000Block066Part004
    + surrogateDiagTailX0RatChunk000Sub000Block066Part005
    + surrogateDiagTailX0RatChunk000Sub000Block066Part006
    + surrogateDiagTailX0RatChunk000Sub000Block066Part007
    + surrogateDiagTailX0RatChunk000Sub000Block066Part008
    + surrogateDiagTailX0RatChunk000Sub000Block066Part009

def surrogateDiagonalTailChunk000Sub000Block066MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block066Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block066Part010
    + surrogateDiagTailX0RatChunk000Sub000Block066Part011
    + surrogateDiagTailX0RatChunk000Sub000Block066Part012
    + surrogateDiagTailX0RatChunk000Sub000Block066Part013
    + surrogateDiagTailX0RatChunk000Sub000Block066Part014
    + surrogateDiagTailX0RatChunk000Sub000Block066Part015
    + surrogateDiagTailX0RatChunk000Sub000Block066Part016
    + surrogateDiagTailX0RatChunk000Sub000Block066Part017
    + surrogateDiagTailX0RatChunk000Sub000Block066Part018
    + surrogateDiagTailX0RatChunk000Sub000Block066Part019

def surrogateDiagonalTailChunk000Sub000Block066TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block066Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block066Part020
    + surrogateDiagTailX0RatChunk000Sub000Block066Part021
    + surrogateDiagTailX0RatChunk000Sub000Block066Part022
    + surrogateDiagTailX0RatChunk000Sub000Block066Part023
    + surrogateDiagTailX0RatChunk000Sub000Block066Part024

def surrogateDiagonalTailChunk000Sub000Block066Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block066HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block066MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block066TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block066 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block066Part000
    + surrogateDiagTailX0RatChunk000Sub000Block066Part001
    + surrogateDiagTailX0RatChunk000Sub000Block066Part002
    + surrogateDiagTailX0RatChunk000Sub000Block066Part003
    + surrogateDiagTailX0RatChunk000Sub000Block066Part004
    + surrogateDiagTailX0RatChunk000Sub000Block066Part005
    + surrogateDiagTailX0RatChunk000Sub000Block066Part006
    + surrogateDiagTailX0RatChunk000Sub000Block066Part007
    + surrogateDiagTailX0RatChunk000Sub000Block066Part008
    + surrogateDiagTailX0RatChunk000Sub000Block066Part009
    + surrogateDiagTailX0RatChunk000Sub000Block066Part010
    + surrogateDiagTailX0RatChunk000Sub000Block066Part011
    + surrogateDiagTailX0RatChunk000Sub000Block066Part012
    + surrogateDiagTailX0RatChunk000Sub000Block066Part013
    + surrogateDiagTailX0RatChunk000Sub000Block066Part014
    + surrogateDiagTailX0RatChunk000Sub000Block066Part015
    + surrogateDiagTailX0RatChunk000Sub000Block066Part016
    + surrogateDiagTailX0RatChunk000Sub000Block066Part017
    + surrogateDiagTailX0RatChunk000Sub000Block066Part018
    + surrogateDiagTailX0RatChunk000Sub000Block066Part019
    + surrogateDiagTailX0RatChunk000Sub000Block066Part020
    + surrogateDiagTailX0RatChunk000Sub000Block066Part021
    + surrogateDiagTailX0RatChunk000Sub000Block066Part022
    + surrogateDiagTailX0RatChunk000Sub000Block066Part023
    + surrogateDiagTailX0RatChunk000Sub000Block066Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block066_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block066Head + surrogateDiagTailX0RatChunk000Sub000Block066Mid + surrogateDiagTailX0RatChunk000Sub000Block066Tail =
      surrogateDiagTailX0RatChunk000Sub000Block066 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block066Head surrogateDiagTailX0RatChunk000Sub000Block066Mid surrogateDiagTailX0RatChunk000Sub000Block066Tail surrogateDiagTailX0RatChunk000Sub000Block066
  ring

def SurrogateDiagonalTailChunk000Sub000Block066HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block066HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block066Head

def SurrogateDiagonalTailChunk000Sub000Block066MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block066MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block066Mid

def SurrogateDiagonalTailChunk000Sub000Block066TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block066TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block066Tail

theorem surrogateDiagonalTailChunk000Sub000Block066_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block066HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block066MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block066TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block066Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block066 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block066HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block066MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block066TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block066Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block066_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
