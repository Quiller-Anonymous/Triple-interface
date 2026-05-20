import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [133,134). -/

/- Block 133 covers tail-support indices [3325,3350) and q from 5521 to 5563. -/

def TailChunk000Sub000Block133Part000SupportExplicit : Finset ℕ :=
  ([5521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part000 : ℚ :=
  (762036025 : ℚ) / 928630965215232

def SurrogateDiagonalTailChunk000Sub000Block133Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5521
    = surrogateDiagTailX0RatChunk000Sub000Block133Part000

theorem surrogateDiagonalTailChunk000Sub000Block133Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part000] using hcert

def TailChunk000Sub000Block133Part001SupportExplicit : Finset ℕ :=
  ([5522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part001 : ℚ :=
  (2320501049 : ℚ) / 488378906250000

def SurrogateDiagonalTailChunk000Sub000Block133Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5522
    = surrogateDiagTailX0RatChunk000Sub000Block133Part001

theorem surrogateDiagonalTailChunk000Sub000Block133Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part001] using hcert

def TailChunk000Sub000Block133Part002SupportExplicit : Finset ℕ :=
  ([5523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part002 : ℚ :=
  (269126887675 : ℚ) / 61079717119283712

def SurrogateDiagonalTailChunk000Sub000Block133Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5523
    = surrogateDiagTailX0RatChunk000Sub000Block133Part002

theorem surrogateDiagonalTailChunk000Sub000Block133Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part002] using hcert

def TailChunk000Sub000Block133Part003SupportExplicit : Finset ℕ :=
  ([5527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part003 : ℚ :=
  (477308265625 : ℚ) / 582921924278251122

def SurrogateDiagonalTailChunk000Sub000Block133Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5527
    = surrogateDiagTailX0RatChunk000Sub000Block133Part003

theorem surrogateDiagonalTailChunk000Sub000Block133Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part003] using hcert

def TailChunk000Sub000Block133Part004SupportExplicit : Finset ℕ :=
  ([5529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part004 : ℚ :=
  (131887738825 : ℚ) / 39635038525980672

def SurrogateDiagonalTailChunk000Sub000Block133Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5529
    = surrogateDiagTailX0RatChunk000Sub000Block133Part004

theorem surrogateDiagonalTailChunk000Sub000Block133Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part004] using hcert

def TailChunk000Sub000Block133Part005SupportExplicit : Finset ℕ :=
  ([5530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part005 : ℚ :=
  (624672364075 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block133Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5530
    = surrogateDiagTailX0RatChunk000Sub000Block133Part005

theorem surrogateDiagonalTailChunk000Sub000Block133Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part005] using hcert

def TailChunk000Sub000Block133Part006SupportExplicit : Finset ℕ :=
  ([5531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part006 : ℚ :=
  (764799025 : ℚ) / 935378483098962

def SurrogateDiagonalTailChunk000Sub000Block133Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5531
    = surrogateDiagTailX0RatChunk000Sub000Block133Part006

theorem surrogateDiagonalTailChunk000Sub000Block133Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part006] using hcert

def TailChunk000Sub000Block133Part007SupportExplicit : Finset ℕ :=
  ([5533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part007 : ℚ :=
  (22726352061 : ℚ) / 21172905739734400

def SurrogateDiagonalTailChunk000Sub000Block133Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5533
    = surrogateDiagTailX0RatChunk000Sub000Block133Part007

theorem surrogateDiagonalTailChunk000Sub000Block133Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part007] using hcert

def TailChunk000Sub000Block133Part008SupportExplicit : Finset ℕ :=
  ([5534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part008 : ℚ :=
  (956844717775 : ℚ) / 146364435462525768

def SurrogateDiagonalTailChunk000Sub000Block133Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5534
    = surrogateDiagTailX0RatChunk000Sub000Block133Part008

theorem surrogateDiagonalTailChunk000Sub000Block133Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part008] using hcert

def TailChunk000Sub000Block133Part009SupportExplicit : Finset ℕ :=
  ([5538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part009 : ℚ :=
  (7674545093 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk000Sub000Block133Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5538
    = surrogateDiagTailX0RatChunk000Sub000Block133Part009

theorem surrogateDiagonalTailChunk000Sub000Block133Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part009] using hcert

def TailChunk000Sub000Block133Part010SupportExplicit : Finset ℕ :=
  ([5539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part010 : ℚ :=
  (5240994299 : ℚ) / 5722757506636800

def SurrogateDiagonalTailChunk000Sub000Block133Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5539
    = surrogateDiagTailX0RatChunk000Sub000Block133Part010

theorem surrogateDiagonalTailChunk000Sub000Block133Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part010] using hcert

def TailChunk000Sub000Block133Part011SupportExplicit : Finset ℕ :=
  ([5541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part011 : ℚ :=
  (127851825 : ℚ) / 46450113346624

def SurrogateDiagonalTailChunk000Sub000Block133Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5541
    = surrogateDiagTailX0RatChunk000Sub000Block133Part011

theorem surrogateDiagonalTailChunk000Sub000Block133Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part011] using hcert

def TailChunk000Sub000Block133Part012SupportExplicit : Finset ℕ :=
  ([5542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part012 : ℚ :=
  (297505022375 : ℚ) / 37622321725833216

def SurrogateDiagonalTailChunk000Sub000Block133Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5542
    = surrogateDiagTailX0RatChunk000Sub000Block133Part012

theorem surrogateDiagonalTailChunk000Sub000Block133Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part012] using hcert

def TailChunk000Sub000Block133Part013SupportExplicit : Finset ℕ :=
  ([5543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part013 : ℚ :=
  (4047984379 : ℚ) / 4318670153318400

def SurrogateDiagonalTailChunk000Sub000Block133Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5543
    = surrogateDiagTailX0RatChunk000Sub000Block133Part013

theorem surrogateDiagonalTailChunk000Sub000Block133Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part013] using hcert

def TailChunk000Sub000Block133Part014SupportExplicit : Finset ℕ :=
  ([5545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part014 : ℚ :=
  (768068457875 : ℚ) / 482387305176121344

def SurrogateDiagonalTailChunk000Sub000Block133Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5545
    = surrogateDiagTailX0RatChunk000Sub000Block133Part014

theorem surrogateDiagonalTailChunk000Sub000Block133Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part014] using hcert

def TailChunk000Sub000Block133Part015SupportExplicit : Finset ℕ :=
  ([5546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part015 : ℚ :=
  (460731987725 : ℚ) / 63349058420948544

def SurrogateDiagonalTailChunk000Sub000Block133Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5546
    = surrogateDiagTailX0RatChunk000Sub000Block133Part015

theorem surrogateDiagonalTailChunk000Sub000Block133Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part015] using hcert

def TailChunk000Sub000Block133Part016SupportExplicit : Finset ℕ :=
  ([5549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part016 : ℚ :=
  (18453578209 : ℚ) / 20332551781216800

def SurrogateDiagonalTailChunk000Sub000Block133Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5549
    = surrogateDiagTailX0RatChunk000Sub000Block133Part016

theorem surrogateDiagonalTailChunk000Sub000Block133Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part016] using hcert

def TailChunk000Sub000Block133Part017SupportExplicit : Finset ℕ :=
  ([5551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part017 : ℚ :=
  (1641013517 : ℚ) / 4354435384934400

def SurrogateDiagonalTailChunk000Sub000Block133Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5551
    = surrogateDiagTailX0RatChunk000Sub000Block133Part017

theorem surrogateDiagonalTailChunk000Sub000Block133Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part017] using hcert

def TailChunk000Sub000Block133Part018SupportExplicit : Finset ℕ :=
  ([5554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part018 : ℚ :=
  (120495765625 : ℚ) / 37123140982927872

def SurrogateDiagonalTailChunk000Sub000Block133Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5554
    = surrogateDiagTailX0RatChunk000Sub000Block133Part018

theorem surrogateDiagonalTailChunk000Sub000Block133Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part018] using hcert

def TailChunk000Sub000Block133Part019SupportExplicit : Finset ℕ :=
  ([5555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part019 : ℚ :=
  (5130741 : ℚ) / 8535040000000

def SurrogateDiagonalTailChunk000Sub000Block133Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5555
    = surrogateDiagTailX0RatChunk000Sub000Block133Part019

theorem surrogateDiagonalTailChunk000Sub000Block133Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part019] using hcert

def TailChunk000Sub000Block133Part020SupportExplicit : Finset ℕ :=
  ([5557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part020 : ℚ :=
  (482503890625 : ℚ) / 595683836311233312

def SurrogateDiagonalTailChunk000Sub000Block133Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5557
    = surrogateDiagTailX0RatChunk000Sub000Block133Part020

theorem surrogateDiagonalTailChunk000Sub000Block133Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part020] using hcert

def TailChunk000Sub000Block133Part021SupportExplicit : Finset ℕ :=
  ([5558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part021 : ℚ :=
  (407756660225 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block133Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5558
    = surrogateDiagTailX0RatChunk000Sub000Block133Part021

theorem surrogateDiagonalTailChunk000Sub000Block133Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part021] using hcert

def TailChunk000Sub000Block133Part022SupportExplicit : Finset ℕ :=
  ([5559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part022 : ℚ :=
  (74490139675 : ℚ) / 22294709170864128

def SurrogateDiagonalTailChunk000Sub000Block133Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5559
    = surrogateDiagTailX0RatChunk000Sub000Block133Part022

theorem surrogateDiagonalTailChunk000Sub000Block133Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part022] using hcert

def TailChunk000Sub000Block133Part023SupportExplicit : Finset ℕ :=
  ([5561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part023 : ℚ :=
  (1876225730275 : ℚ) / 2145151703515632768

def SurrogateDiagonalTailChunk000Sub000Block133Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5561
    = surrogateDiagTailX0RatChunk000Sub000Block133Part023

theorem surrogateDiagonalTailChunk000Sub000Block133Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part023] using hcert

def TailChunk000Sub000Block133Part024SupportExplicit : Finset ℕ :=
  ([5563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block133Part024 : ℚ :=
  (483546390625 : ℚ) / 598261155800709042

def SurrogateDiagonalTailChunk000Sub000Block133Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5563
    = surrogateDiagTailX0RatChunk000Sub000Block133Part024

theorem surrogateDiagonalTailChunk000Sub000Block133Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block133Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block133Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block133Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block133Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block133Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block133Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block133HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block133Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block133Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block133Part000
    + surrogateDiagTailX0RatChunk000Sub000Block133Part001
    + surrogateDiagTailX0RatChunk000Sub000Block133Part002
    + surrogateDiagTailX0RatChunk000Sub000Block133Part003
    + surrogateDiagTailX0RatChunk000Sub000Block133Part004
    + surrogateDiagTailX0RatChunk000Sub000Block133Part005
    + surrogateDiagTailX0RatChunk000Sub000Block133Part006
    + surrogateDiagTailX0RatChunk000Sub000Block133Part007
    + surrogateDiagTailX0RatChunk000Sub000Block133Part008
    + surrogateDiagTailX0RatChunk000Sub000Block133Part009

def surrogateDiagonalTailChunk000Sub000Block133MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block133Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block133Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block133Part010
    + surrogateDiagTailX0RatChunk000Sub000Block133Part011
    + surrogateDiagTailX0RatChunk000Sub000Block133Part012
    + surrogateDiagTailX0RatChunk000Sub000Block133Part013
    + surrogateDiagTailX0RatChunk000Sub000Block133Part014
    + surrogateDiagTailX0RatChunk000Sub000Block133Part015
    + surrogateDiagTailX0RatChunk000Sub000Block133Part016
    + surrogateDiagTailX0RatChunk000Sub000Block133Part017
    + surrogateDiagTailX0RatChunk000Sub000Block133Part018
    + surrogateDiagTailX0RatChunk000Sub000Block133Part019

def surrogateDiagonalTailChunk000Sub000Block133TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block133Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block133Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block133Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block133Part020
    + surrogateDiagTailX0RatChunk000Sub000Block133Part021
    + surrogateDiagTailX0RatChunk000Sub000Block133Part022
    + surrogateDiagTailX0RatChunk000Sub000Block133Part023
    + surrogateDiagTailX0RatChunk000Sub000Block133Part024

def surrogateDiagonalTailChunk000Sub000Block133Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block133HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block133MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block133TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block133 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block133Part000
    + surrogateDiagTailX0RatChunk000Sub000Block133Part001
    + surrogateDiagTailX0RatChunk000Sub000Block133Part002
    + surrogateDiagTailX0RatChunk000Sub000Block133Part003
    + surrogateDiagTailX0RatChunk000Sub000Block133Part004
    + surrogateDiagTailX0RatChunk000Sub000Block133Part005
    + surrogateDiagTailX0RatChunk000Sub000Block133Part006
    + surrogateDiagTailX0RatChunk000Sub000Block133Part007
    + surrogateDiagTailX0RatChunk000Sub000Block133Part008
    + surrogateDiagTailX0RatChunk000Sub000Block133Part009
    + surrogateDiagTailX0RatChunk000Sub000Block133Part010
    + surrogateDiagTailX0RatChunk000Sub000Block133Part011
    + surrogateDiagTailX0RatChunk000Sub000Block133Part012
    + surrogateDiagTailX0RatChunk000Sub000Block133Part013
    + surrogateDiagTailX0RatChunk000Sub000Block133Part014
    + surrogateDiagTailX0RatChunk000Sub000Block133Part015
    + surrogateDiagTailX0RatChunk000Sub000Block133Part016
    + surrogateDiagTailX0RatChunk000Sub000Block133Part017
    + surrogateDiagTailX0RatChunk000Sub000Block133Part018
    + surrogateDiagTailX0RatChunk000Sub000Block133Part019
    + surrogateDiagTailX0RatChunk000Sub000Block133Part020
    + surrogateDiagTailX0RatChunk000Sub000Block133Part021
    + surrogateDiagTailX0RatChunk000Sub000Block133Part022
    + surrogateDiagTailX0RatChunk000Sub000Block133Part023
    + surrogateDiagTailX0RatChunk000Sub000Block133Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block133_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block133Head + surrogateDiagTailX0RatChunk000Sub000Block133Mid + surrogateDiagTailX0RatChunk000Sub000Block133Tail =
      surrogateDiagTailX0RatChunk000Sub000Block133 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block133Head surrogateDiagTailX0RatChunk000Sub000Block133Mid surrogateDiagTailX0RatChunk000Sub000Block133Tail surrogateDiagTailX0RatChunk000Sub000Block133
  ring

def SurrogateDiagonalTailChunk000Sub000Block133HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block133HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block133Head

def SurrogateDiagonalTailChunk000Sub000Block133MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block133MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block133Mid

def SurrogateDiagonalTailChunk000Sub000Block133TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block133TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block133Tail

theorem surrogateDiagonalTailChunk000Sub000Block133_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block133HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block133MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block133TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block133Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block133 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block133HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block133MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block133TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block133Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block133_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
