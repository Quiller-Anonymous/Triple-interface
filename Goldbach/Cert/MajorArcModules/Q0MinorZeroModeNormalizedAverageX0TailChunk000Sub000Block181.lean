import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [181,182). -/

/-- Block 181 covers tail-support indices [4525,4550) and q from 7493 to 7534. -/

def TailChunk000Sub000Block181Part000SupportExplicit : Finset ℕ :=
  ([7493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part000 : ℚ :=
  (377133259625 : ℚ) / 792462105816377472

def SurrogateDiagonalTailChunk000Sub000Block181Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7493
    = surrogateDiagTailX0RatChunk000Sub000Block181Part000

theorem surrogateDiagonalTailChunk000Sub000Block181Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part000] using hcert

def TailChunk000Sub000Block181Part001SupportExplicit : Finset ℕ :=
  ([7494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part001 : ℚ :=
  (682149594025 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block181Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7494
    = surrogateDiagTailX0RatChunk000Sub000Block181Part001

theorem surrogateDiagonalTailChunk000Sub000Block181Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part001] using hcert

def TailChunk000Sub000Block181Part002SupportExplicit : Finset ℕ :=
  ([7495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part002 : ℚ :=
  (120292736925 : ℚ) / 153495194295052288

def SurrogateDiagonalTailChunk000Sub000Block181Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7495
    = surrogateDiagTailX0RatChunk000Sub000Block181Part002

theorem surrogateDiagonalTailChunk000Sub000Block181Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part002] using hcert

def TailChunk000Sub000Block181Part003SupportExplicit : Finset ℕ :=
  ([7498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part003 : ℚ :=
  (850068678475 : ℚ) / 403438778604436608

def SurrogateDiagonalTailChunk000Sub000Block181Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7498
    = surrogateDiagTailX0RatChunk000Sub000Block181Part003

theorem surrogateDiagonalTailChunk000Sub000Block181Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part003] using hcert

def TailChunk000Sub000Block181Part004SupportExplicit : Finset ℕ :=
  ([7499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part004 : ℚ :=
  (878671890625 : ℚ) / 1975825617206230002

def SurrogateDiagonalTailChunk000Sub000Block181Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7499
    = surrogateDiagTailX0RatChunk000Sub000Block181Part004

theorem surrogateDiagonalTailChunk000Sub000Block181Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part004] using hcert

def TailChunk000Sub000Block181Part005SupportExplicit : Finset ℕ :=
  ([7501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part005 : ℚ :=
  (456623375 : ℚ) / 825729969291264

def SurrogateDiagonalTailChunk000Sub000Block181Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7501
    = surrogateDiagTailX0RatChunk000Sub000Block181Part005

theorem surrogateDiagonalTailChunk000Sub000Block181Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part005] using hcert

def TailChunk000Sub000Block181Part006SupportExplicit : Finset ℕ :=
  ([7503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part006 : ℚ :=
  (74405388433 : ℚ) / 53094776832000000

def SurrogateDiagonalTailChunk000Sub000Block181Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7503
    = surrogateDiagTailX0RatChunk000Sub000Block181Part006

theorem surrogateDiagonalTailChunk000Sub000Block181Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part006] using hcert

def TailChunk000Sub000Block181Part007SupportExplicit : Finset ℕ :=
  ([7505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part007 : ℚ :=
  (582791433925 : ℚ) / 621835145145556992

def SurrogateDiagonalTailChunk000Sub000Block181Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7505
    = surrogateDiagTailX0RatChunk000Sub000Block181Part007

theorem surrogateDiagonalTailChunk000Sub000Block181Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part007] using hcert

def TailChunk000Sub000Block181Part008SupportExplicit : Finset ℕ :=
  ([7507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part008 : ℚ :=
  (880547640625 : ℚ) / 1984271560257870162

def SurrogateDiagonalTailChunk000Sub000Block181Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7507
    = surrogateDiagTailX0RatChunk000Sub000Block181Part008

theorem surrogateDiagonalTailChunk000Sub000Block181Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part008] using hcert

def TailChunk000Sub000Block181Part009SupportExplicit : Finset ℕ :=
  ([7509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part009 : ℚ :=
  (489297281275 : ℚ) / 391954876100320032

def SurrogateDiagonalTailChunk000Sub000Block181Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7509
    = surrogateDiagTailX0RatChunk000Sub000Block181Part009

theorem surrogateDiagonalTailChunk000Sub000Block181Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part009] using hcert

def TailChunk000Sub000Block181Part010SupportExplicit : Finset ℕ :=
  ([7510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part010 : ℚ :=
  (10330849493 : ℚ) / 2700540000000000

def SurrogateDiagonalTailChunk000Sub000Block181Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7510
    = surrogateDiagTailX0RatChunk000Sub000Block181Part010

theorem surrogateDiagonalTailChunk000Sub000Block181Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part010] using hcert

def TailChunk000Sub000Block181Part011SupportExplicit : Finset ℕ :=
  ([7511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part011 : ℚ :=
  (7730536075 : ℚ) / 9753935262253056

def SurrogateDiagonalTailChunk000Sub000Block181Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7511
    = surrogateDiagTailX0RatChunk000Sub000Block181Part011

theorem surrogateDiagonalTailChunk000Sub000Block181Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part011] using hcert

def TailChunk000Sub000Block181Part012SupportExplicit : Finset ℕ :=
  ([7513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part012 : ℚ :=
  (224370301 : ℚ) / 393424733532864

def SurrogateDiagonalTailChunk000Sub000Block181Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7513
    = surrogateDiagTailX0RatChunk000Sub000Block181Part012

theorem surrogateDiagonalTailChunk000Sub000Block181Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part012] using hcert

def TailChunk000Sub000Block181Part013SupportExplicit : Finset ℕ :=
  ([7517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part013 : ℚ :=
  (882895140625 : ℚ) / 1994867032968828192

def SurrogateDiagonalTailChunk000Sub000Block181Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7517
    = surrogateDiagTailX0RatChunk000Sub000Block181Part013

theorem surrogateDiagonalTailChunk000Sub000Block181Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part013] using hcert

def TailChunk000Sub000Block181Part014SupportExplicit : Finset ℕ :=
  ([7518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part014 : ℚ :=
  (22144824725 : ℚ) / 1927827131848704

def SurrogateDiagonalTailChunk000Sub000Block181Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7518
    = surrogateDiagTailX0RatChunk000Sub000Block181Part014

theorem surrogateDiagonalTailChunk000Sub000Block181Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part014] using hcert

def TailChunk000Sub000Block181Part015SupportExplicit : Finset ℕ :=
  ([7519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part015 : ℚ :=
  (3424070537425 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub000Block181Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7519
    = surrogateDiagTailX0RatChunk000Sub000Block181Part015

theorem surrogateDiagonalTailChunk000Sub000Block181Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part015] using hcert

def TailChunk000Sub000Block181Part016SupportExplicit : Finset ℕ :=
  ([7521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part016 : ℚ :=
  (1840694716225 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub000Block181Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7521
    = surrogateDiagTailX0RatChunk000Sub000Block181Part016

theorem surrogateDiagonalTailChunk000Sub000Block181Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part016] using hcert

def TailChunk000Sub000Block181Part017SupportExplicit : Finset ℕ :=
  ([7522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part017 : ℚ :=
  (70711459879 : ℚ) / 19991170810675200

def SurrogateDiagonalTailChunk000Sub000Block181Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7522
    = surrogateDiagTailX0RatChunk000Sub000Block181Part017

theorem surrogateDiagonalTailChunk000Sub000Block181Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part017] using hcert

def TailChunk000Sub000Block181Part018SupportExplicit : Finset ℕ :=
  ([7523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part018 : ℚ :=
  (884305140625 : ℚ) / 2001244649942619282

def SurrogateDiagonalTailChunk000Sub000Block181Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7523
    = surrogateDiagTailX0RatChunk000Sub000Block181Part018

theorem surrogateDiagonalTailChunk000Sub000Block181Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part018] using hcert

def TailChunk000Sub000Block181Part019SupportExplicit : Finset ℕ :=
  ([7526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part019 : ℚ :=
  (67732139113 : ℚ) / 17558701054003200

def SurrogateDiagonalTailChunk000Sub000Block181Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7526
    = surrogateDiagTailX0RatChunk000Sub000Block181Part019

theorem surrogateDiagonalTailChunk000Sub000Block181Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part019] using hcert

def TailChunk000Sub000Block181Part020SupportExplicit : Finset ℕ :=
  ([7527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part020 : ℚ :=
  (444302410975 : ℚ) / 281849162851418112

def SurrogateDiagonalTailChunk000Sub000Block181Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7527
    = surrogateDiagTailX0RatChunk000Sub000Block181Part020

theorem surrogateDiagonalTailChunk000Sub000Block181Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part020] using hcert

def TailChunk000Sub000Block181Part021SupportExplicit : Finset ℕ :=
  ([7529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part021 : ℚ :=
  (885716265625 : ℚ) / 2007637546704056832

def SurrogateDiagonalTailChunk000Sub000Block181Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7529
    = surrogateDiagTailX0RatChunk000Sub000Block181Part021

theorem surrogateDiagonalTailChunk000Sub000Block181Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part021] using hcert

def TailChunk000Sub000Block181Part022SupportExplicit : Finset ℕ :=
  ([7530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part022 : ℚ :=
  (29320311937 : ℚ) / 1600320000000000

def SurrogateDiagonalTailChunk000Sub000Block181Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7530
    = surrogateDiagTailX0RatChunk000Sub000Block181Part022

theorem surrogateDiagonalTailChunk000Sub000Block181Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part022] using hcert

def TailChunk000Sub000Block181Part023SupportExplicit : Finset ℕ :=
  ([7531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part023 : ℚ :=
  (135561255525 : ℚ) / 260606128909647872

def SurrogateDiagonalTailChunk000Sub000Block181Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7531
    = surrogateDiagTailX0RatChunk000Sub000Block181Part023

theorem surrogateDiagonalTailChunk000Sub000Block181Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part023] using hcert

def TailChunk000Sub000Block181Part024SupportExplicit : Finset ℕ :=
  ([7534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block181Part024 : ℚ :=
  (1773431367775 : ℚ) / 502976994672717768

def SurrogateDiagonalTailChunk000Sub000Block181Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7534
    = surrogateDiagTailX0RatChunk000Sub000Block181Part024

theorem surrogateDiagonalTailChunk000Sub000Block181Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block181Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block181Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block181Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block181Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block181Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block181HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block181Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part000
    + surrogateDiagTailX0RatChunk000Sub000Block181Part001
    + surrogateDiagTailX0RatChunk000Sub000Block181Part002
    + surrogateDiagTailX0RatChunk000Sub000Block181Part003
    + surrogateDiagTailX0RatChunk000Sub000Block181Part004
    + surrogateDiagTailX0RatChunk000Sub000Block181Part005
    + surrogateDiagTailX0RatChunk000Sub000Block181Part006
    + surrogateDiagTailX0RatChunk000Sub000Block181Part007
    + surrogateDiagTailX0RatChunk000Sub000Block181Part008
    + surrogateDiagTailX0RatChunk000Sub000Block181Part009

def surrogateDiagonalTailChunk000Sub000Block181MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block181Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part010
    + surrogateDiagTailX0RatChunk000Sub000Block181Part011
    + surrogateDiagTailX0RatChunk000Sub000Block181Part012
    + surrogateDiagTailX0RatChunk000Sub000Block181Part013
    + surrogateDiagTailX0RatChunk000Sub000Block181Part014
    + surrogateDiagTailX0RatChunk000Sub000Block181Part015
    + surrogateDiagTailX0RatChunk000Sub000Block181Part016
    + surrogateDiagTailX0RatChunk000Sub000Block181Part017
    + surrogateDiagTailX0RatChunk000Sub000Block181Part018
    + surrogateDiagTailX0RatChunk000Sub000Block181Part019

def surrogateDiagonalTailChunk000Sub000Block181TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block181Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part020
    + surrogateDiagTailX0RatChunk000Sub000Block181Part021
    + surrogateDiagTailX0RatChunk000Sub000Block181Part022
    + surrogateDiagTailX0RatChunk000Sub000Block181Part023
    + surrogateDiagTailX0RatChunk000Sub000Block181Part024

def surrogateDiagonalTailChunk000Sub000Block181Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block181HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block181MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block181TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block181 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block181Part000
    + surrogateDiagTailX0RatChunk000Sub000Block181Part001
    + surrogateDiagTailX0RatChunk000Sub000Block181Part002
    + surrogateDiagTailX0RatChunk000Sub000Block181Part003
    + surrogateDiagTailX0RatChunk000Sub000Block181Part004
    + surrogateDiagTailX0RatChunk000Sub000Block181Part005
    + surrogateDiagTailX0RatChunk000Sub000Block181Part006
    + surrogateDiagTailX0RatChunk000Sub000Block181Part007
    + surrogateDiagTailX0RatChunk000Sub000Block181Part008
    + surrogateDiagTailX0RatChunk000Sub000Block181Part009
    + surrogateDiagTailX0RatChunk000Sub000Block181Part010
    + surrogateDiagTailX0RatChunk000Sub000Block181Part011
    + surrogateDiagTailX0RatChunk000Sub000Block181Part012
    + surrogateDiagTailX0RatChunk000Sub000Block181Part013
    + surrogateDiagTailX0RatChunk000Sub000Block181Part014
    + surrogateDiagTailX0RatChunk000Sub000Block181Part015
    + surrogateDiagTailX0RatChunk000Sub000Block181Part016
    + surrogateDiagTailX0RatChunk000Sub000Block181Part017
    + surrogateDiagTailX0RatChunk000Sub000Block181Part018
    + surrogateDiagTailX0RatChunk000Sub000Block181Part019
    + surrogateDiagTailX0RatChunk000Sub000Block181Part020
    + surrogateDiagTailX0RatChunk000Sub000Block181Part021
    + surrogateDiagTailX0RatChunk000Sub000Block181Part022
    + surrogateDiagTailX0RatChunk000Sub000Block181Part023
    + surrogateDiagTailX0RatChunk000Sub000Block181Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block181_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block181Head + surrogateDiagTailX0RatChunk000Sub000Block181Mid + surrogateDiagTailX0RatChunk000Sub000Block181Tail =
      surrogateDiagTailX0RatChunk000Sub000Block181 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block181Head surrogateDiagTailX0RatChunk000Sub000Block181Mid surrogateDiagTailX0RatChunk000Sub000Block181Tail surrogateDiagTailX0RatChunk000Sub000Block181
  ring

def SurrogateDiagonalTailChunk000Sub000Block181HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block181HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block181Head

def SurrogateDiagonalTailChunk000Sub000Block181MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block181MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block181Mid

def SurrogateDiagonalTailChunk000Sub000Block181TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block181TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block181Tail

theorem surrogateDiagonalTailChunk000Sub000Block181_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block181HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block181MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block181TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block181Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block181 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block181HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block181MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block181TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block181Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block181_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
