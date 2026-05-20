import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [68,69). -/

/- Block 068 covers tail-support indices [1700,1725) and q from 2847 to 2893. -/

def TailChunk000Sub000Block068Part000SupportExplicit : Finset ℕ :=
  ([2847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part000 : ℚ :=
  (67433719775 : ℚ) / 2477189907873792

def SurrogateDiagonalTailChunk000Sub000Block068Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2847
    = surrogateDiagTailX0RatChunk000Sub000Block068Part000

theorem surrogateDiagonalTailChunk000Sub000Block068Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part000] using hcert

def TailChunk000Sub000Block068Part001SupportExplicit : Finset ℕ :=
  ([2849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part001 : ℚ :=
  (9876070141 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub000Block068Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2849
    = surrogateDiagTailX0RatChunk000Sub000Block068Part001

theorem surrogateDiagonalTailChunk000Sub000Block068Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part001] using hcert

def TailChunk000Sub000Block068Part002SupportExplicit : Finset ℕ :=
  ([2851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part002 : ℚ :=
  (40632876799 : ℚ) / 6598820125125000

def SurrogateDiagonalTailChunk000Sub000Block068Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2851
    = surrogateDiagTailX0RatChunk000Sub000Block068Part002

theorem surrogateDiagonalTailChunk000Sub000Block068Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part002] using hcert

def TailChunk000Sub000Block068Part003SupportExplicit : Finset ℕ :=
  ([2854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part003 : ℚ :=
  (127219654275 : ℚ) / 3446543039587096

def SurrogateDiagonalTailChunk000Sub000Block068Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2854
    = surrogateDiagTailX0RatChunk000Sub000Block068Part003

theorem surrogateDiagonalTailChunk000Sub000Block068Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part003] using hcert

def TailChunk000Sub000Block068Part004SupportExplicit : Finset ℕ :=
  ([2855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part004 : ℚ :=
  (4886317831 : ℚ) / 675719180812800

def SurrogateDiagonalTailChunk000Sub000Block068Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2855
    = surrogateDiagTailX0RatChunk000Sub000Block068Part004

theorem surrogateDiagonalTailChunk000Sub000Block068Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part004] using hcert

def TailChunk000Sub000Block068Part005SupportExplicit : Finset ℕ :=
  ([2857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part005 : ℚ :=
  (127538265625 : ℚ) / 41591030401331712

def SurrogateDiagonalTailChunk000Sub000Block068Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2857
    = surrogateDiagTailX0RatChunk000Sub000Block068Part005

theorem surrogateDiagonalTailChunk000Sub000Block068Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part005] using hcert

def TailChunk000Sub000Block068Part006SupportExplicit : Finset ℕ :=
  ([2858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part006 : ℚ :=
  (255101971925 : ℚ) / 5198878800166464

def SurrogateDiagonalTailChunk000Sub000Block068Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2858
    = surrogateDiagTailX0RatChunk000Sub000Block068Part006

theorem surrogateDiagonalTailChunk000Sub000Block068Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part006] using hcert

def TailChunk000Sub000Block068Part007SupportExplicit : Finset ℕ :=
  ([2859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part007 : ℚ :=
  (623821826575 : ℚ) / 32862048712163328

def SurrogateDiagonalTailChunk000Sub000Block068Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2859
    = surrogateDiagTailX0RatChunk000Sub000Block068Part007

theorem surrogateDiagonalTailChunk000Sub000Block068Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part007] using hcert

def TailChunk000Sub000Block068Part008SupportExplicit : Finset ℕ :=
  ([2861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part008 : ℚ :=
  (40918419679 : ℚ) / 6691923733123200

def SurrogateDiagonalTailChunk000Sub000Block068Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2861
    = surrogateDiagTailX0RatChunk000Sub000Block068Part008

theorem surrogateDiagonalTailChunk000Sub000Block068Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part008] using hcert

def TailChunk000Sub000Block068Part009SupportExplicit : Finset ℕ :=
  ([2863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part009 : ℚ :=
  (427579943225 : ℚ) / 44899604664827904

def SurrogateDiagonalTailChunk000Sub000Block068Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2863
    = surrogateDiagTailX0RatChunk000Sub000Block068Part009

theorem surrogateDiagonalTailChunk000Sub000Block068Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part009] using hcert

def TailChunk000Sub000Block068Part010SupportExplicit : Finset ℕ :=
  ([2865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part010 : ℚ :=
  (3296269209 : ℚ) / 88983595827200

def SurrogateDiagonalTailChunk000Sub000Block068Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2865
    = surrogateDiagTailX0RatChunk000Sub000Block068Part010

theorem surrogateDiagonalTailChunk000Sub000Block068Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part010] using hcert

def TailChunk000Sub000Block068Part011SupportExplicit : Finset ℕ :=
  ([2866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part011 : ℚ :=
  (256532113325 : ℚ) / 5257374751417344

def SurrogateDiagonalTailChunk000Sub000Block068Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2866
    = surrogateDiagTailX0RatChunk000Sub000Block068Part011

theorem surrogateDiagonalTailChunk000Sub000Block068Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part011] using hcert

def TailChunk000Sub000Block068Part012SupportExplicit : Finset ℕ :=
  ([2867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part012 : ℚ :=
  (39377789539 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub000Block068Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2867
    = surrogateDiagTailX0RatChunk000Sub000Block068Part012

theorem surrogateDiagonalTailChunk000Sub000Block068Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part012] using hcert

def TailChunk000Sub000Block068Part013SupportExplicit : Finset ℕ :=
  ([2869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part013 : ℚ :=
  (853873841 : ℚ) / 118121619600000

def SurrogateDiagonalTailChunk000Sub000Block068Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2869
    = surrogateDiagTailX0RatChunk000Sub000Block068Part013

theorem surrogateDiagonalTailChunk000Sub000Block068Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part013] using hcert

def TailChunk000Sub000Block068Part014SupportExplicit : Finset ℕ :=
  ([2870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part014 : ℚ :=
  (605757239 : ℚ) / 4719535718400

def SurrogateDiagonalTailChunk000Sub000Block068Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2870
    = surrogateDiagTailX0RatChunk000Sub000Block068Part014

theorem surrogateDiagonalTailChunk000Sub000Block068Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part014] using hcert

def TailChunk000Sub000Block068Part015SupportExplicit : Finset ℕ :=
  ([2874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part015 : ℚ :=
  (329132383375 : ℚ) / 2088615169746048

def SurrogateDiagonalTailChunk000Sub000Block068Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2874
    = surrogateDiagTailX0RatChunk000Sub000Block068Part015

theorem surrogateDiagonalTailChunk000Sub000Block068Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part015] using hcert

def TailChunk000Sub000Block068Part016SupportExplicit : Finset ℕ :=
  ([2877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part016 : ℚ :=
  (266629934225 : ℚ) / 8869057711570944

def SurrogateDiagonalTailChunk000Sub000Block068Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2877
    = surrogateDiagTailX0RatChunk000Sub000Block068Part016

theorem surrogateDiagonalTailChunk000Sub000Block068Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part016] using hcert

def TailChunk000Sub000Block068Part017SupportExplicit : Finset ℕ :=
  ([2878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part017 : ℚ :=
  (129368294475 : ℚ) / 3564028336748056

def SurrogateDiagonalTailChunk000Sub000Block068Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2878
    = surrogateDiagTailX0RatChunk000Sub000Block068Part017

theorem surrogateDiagonalTailChunk000Sub000Block068Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part017] using hcert

def TailChunk000Sub000Block068Part018SupportExplicit : Finset ℕ :=
  ([2879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part018 : ℚ :=
  (1035872908975 : ℚ) / 171549721477318728

def SurrogateDiagonalTailChunk000Sub000Block068Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2879
    = surrogateDiagTailX0RatChunk000Sub000Block068Part018

theorem surrogateDiagonalTailChunk000Sub000Block068Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part018] using hcert

def TailChunk000Sub000Block068Part019SupportExplicit : Finset ℕ :=
  ([2881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part019 : ℚ :=
  (993544109725 : ℚ) / 147638547085696128

def SurrogateDiagonalTailChunk000Sub000Block068Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2881
    = surrogateDiagTailX0RatChunk000Sub000Block068Part019

theorem surrogateDiagonalTailChunk000Sub000Block068Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part019] using hcert

def TailChunk000Sub000Block068Part020SupportExplicit : Finset ℕ :=
  ([2882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part020 : ℚ :=
  (2307989543 : ℚ) / 35708390250000

def SurrogateDiagonalTailChunk000Sub000Block068Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2882
    = surrogateDiagTailX0RatChunk000Sub000Block068Part020

theorem surrogateDiagonalTailChunk000Sub000Block068Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part020] using hcert

def TailChunk000Sub000Block068Part021SupportExplicit : Finset ℕ :=
  ([2885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part021 : ℚ :=
  (7501022675 : ℚ) / 652428617711616

def SurrogateDiagonalTailChunk000Sub000Block068Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2885
    = surrogateDiagTailX0RatChunk000Sub000Block068Part021

theorem surrogateDiagonalTailChunk000Sub000Block068Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part021] using hcert

def TailChunk000Sub000Block068Part022SupportExplicit : Finset ℕ :=
  ([2886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part022 : ℚ :=
  (9233536625 : ℚ) / 51608123080704

def SurrogateDiagonalTailChunk000Sub000Block068Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2886
    = surrogateDiagTailX0RatChunk000Sub000Block068Part022

theorem surrogateDiagonalTailChunk000Sub000Block068Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part022] using hcert

def TailChunk000Sub000Block068Part023SupportExplicit : Finset ℕ :=
  ([2887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part023 : ℚ :=
  (130230765625 : ℚ) / 43366280501806002

def SurrogateDiagonalTailChunk000Sub000Block068Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2887
    = surrogateDiagTailX0RatChunk000Sub000Block068Part023

theorem surrogateDiagonalTailChunk000Sub000Block068Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part023] using hcert

def TailChunk000Sub000Block068Part024SupportExplicit : Finset ℕ :=
  ([2893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block068Part024 : ℚ :=
  (4671388397 : ℚ) / 589117641968400

def SurrogateDiagonalTailChunk000Sub000Block068Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2893
    = surrogateDiagTailX0RatChunk000Sub000Block068Part024

theorem surrogateDiagonalTailChunk000Sub000Block068Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block068Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block068Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block068Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block068Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block068Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block068HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block068Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block068Part000
    + surrogateDiagTailX0RatChunk000Sub000Block068Part001
    + surrogateDiagTailX0RatChunk000Sub000Block068Part002
    + surrogateDiagTailX0RatChunk000Sub000Block068Part003
    + surrogateDiagTailX0RatChunk000Sub000Block068Part004
    + surrogateDiagTailX0RatChunk000Sub000Block068Part005
    + surrogateDiagTailX0RatChunk000Sub000Block068Part006
    + surrogateDiagTailX0RatChunk000Sub000Block068Part007
    + surrogateDiagTailX0RatChunk000Sub000Block068Part008
    + surrogateDiagTailX0RatChunk000Sub000Block068Part009

def surrogateDiagonalTailChunk000Sub000Block068MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block068Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block068Part010
    + surrogateDiagTailX0RatChunk000Sub000Block068Part011
    + surrogateDiagTailX0RatChunk000Sub000Block068Part012
    + surrogateDiagTailX0RatChunk000Sub000Block068Part013
    + surrogateDiagTailX0RatChunk000Sub000Block068Part014
    + surrogateDiagTailX0RatChunk000Sub000Block068Part015
    + surrogateDiagTailX0RatChunk000Sub000Block068Part016
    + surrogateDiagTailX0RatChunk000Sub000Block068Part017
    + surrogateDiagTailX0RatChunk000Sub000Block068Part018
    + surrogateDiagTailX0RatChunk000Sub000Block068Part019

def surrogateDiagonalTailChunk000Sub000Block068TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block068Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block068Part020
    + surrogateDiagTailX0RatChunk000Sub000Block068Part021
    + surrogateDiagTailX0RatChunk000Sub000Block068Part022
    + surrogateDiagTailX0RatChunk000Sub000Block068Part023
    + surrogateDiagTailX0RatChunk000Sub000Block068Part024

def surrogateDiagonalTailChunk000Sub000Block068Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block068HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block068MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block068TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block068 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block068Part000
    + surrogateDiagTailX0RatChunk000Sub000Block068Part001
    + surrogateDiagTailX0RatChunk000Sub000Block068Part002
    + surrogateDiagTailX0RatChunk000Sub000Block068Part003
    + surrogateDiagTailX0RatChunk000Sub000Block068Part004
    + surrogateDiagTailX0RatChunk000Sub000Block068Part005
    + surrogateDiagTailX0RatChunk000Sub000Block068Part006
    + surrogateDiagTailX0RatChunk000Sub000Block068Part007
    + surrogateDiagTailX0RatChunk000Sub000Block068Part008
    + surrogateDiagTailX0RatChunk000Sub000Block068Part009
    + surrogateDiagTailX0RatChunk000Sub000Block068Part010
    + surrogateDiagTailX0RatChunk000Sub000Block068Part011
    + surrogateDiagTailX0RatChunk000Sub000Block068Part012
    + surrogateDiagTailX0RatChunk000Sub000Block068Part013
    + surrogateDiagTailX0RatChunk000Sub000Block068Part014
    + surrogateDiagTailX0RatChunk000Sub000Block068Part015
    + surrogateDiagTailX0RatChunk000Sub000Block068Part016
    + surrogateDiagTailX0RatChunk000Sub000Block068Part017
    + surrogateDiagTailX0RatChunk000Sub000Block068Part018
    + surrogateDiagTailX0RatChunk000Sub000Block068Part019
    + surrogateDiagTailX0RatChunk000Sub000Block068Part020
    + surrogateDiagTailX0RatChunk000Sub000Block068Part021
    + surrogateDiagTailX0RatChunk000Sub000Block068Part022
    + surrogateDiagTailX0RatChunk000Sub000Block068Part023
    + surrogateDiagTailX0RatChunk000Sub000Block068Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block068_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block068Head + surrogateDiagTailX0RatChunk000Sub000Block068Mid + surrogateDiagTailX0RatChunk000Sub000Block068Tail =
      surrogateDiagTailX0RatChunk000Sub000Block068 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block068Head surrogateDiagTailX0RatChunk000Sub000Block068Mid surrogateDiagTailX0RatChunk000Sub000Block068Tail surrogateDiagTailX0RatChunk000Sub000Block068
  ring

def SurrogateDiagonalTailChunk000Sub000Block068HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block068HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block068Head

def SurrogateDiagonalTailChunk000Sub000Block068MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block068MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block068Mid

def SurrogateDiagonalTailChunk000Sub000Block068TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block068TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block068Tail

theorem surrogateDiagonalTailChunk000Sub000Block068_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block068HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block068MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block068TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block068Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block068 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block068HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block068MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block068TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block068Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block068_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
