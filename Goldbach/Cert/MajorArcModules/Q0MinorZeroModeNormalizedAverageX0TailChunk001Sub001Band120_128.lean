import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [120,129). -/

/-- Block 120 covers tail-support indices [18000,18025) and q from 29653 to 29690. -/

def TailChunk001Sub001Block120Part000SupportExplicit : Finset ℕ :=
  ([29653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part000 : ℚ :=
  (1884632012671 : ℚ) / 56046851733336883200

def SurrogateDiagonalTailChunk001Sub001Block120Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29653
    = surrogateDiagTailX0RatChunk001Sub001Block120Part000

theorem surrogateDiagonalTailChunk001Sub001Block120Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part000] using hcert

def TailChunk001Sub001Block120Part001SupportExplicit : Finset ℕ :=
  ([29654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part001 : ℚ :=
  (3434998890625 : ℚ) / 30203887966677009522

def SurrogateDiagonalTailChunk001Sub001Block120Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29654
    = surrogateDiagTailX0RatChunk001Sub001Block120Part001

theorem surrogateDiagonalTailChunk001Sub001Block120Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part001] using hcert

def TailChunk001Sub001Block120Part002SupportExplicit : Finset ℕ :=
  ([29657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part002 : ℚ :=
  (526808143423 : ℚ) / 17636824096291360800

def SurrogateDiagonalTailChunk001Sub001Block120Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29657
    = surrogateDiagTailX0RatChunk001Sub001Block120Part002

theorem surrogateDiagonalTailChunk001Sub001Block120Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part002] using hcert

def TailChunk001Sub001Block120Part003SupportExplicit : Finset ℕ :=
  ([29658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part003 : ℚ :=
  (6106465505725 : ℚ) / 23864800368732451968

def SurrogateDiagonalTailChunk001Sub001Block120Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29658
    = surrogateDiagTailX0RatChunk001Sub001Block120Part003

theorem surrogateDiagonalTailChunk001Sub001Block120Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part003] using hcert

def TailChunk001Sub001Block120Part004SupportExplicit : Finset ℕ :=
  ([29659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part004 : ℚ :=
  (36239911117075 : ℚ) / 826292438765734053888

def SurrogateDiagonalTailChunk001Sub001Block120Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29659
    = surrogateDiagTailX0RatChunk001Sub001Block120Part004

theorem surrogateDiagonalTailChunk001Sub001Block120Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part004] using hcert

def TailChunk001Sub001Block120Part005SupportExplicit : Finset ℕ :=
  ([29661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part005 : ℚ :=
  (24433873011325 : ℚ) / 382145954193497728128

def SurrogateDiagonalTailChunk001Sub001Block120Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29661
    = surrogateDiagTailX0RatChunk001Sub001Block120Part005

theorem surrogateDiagonalTailChunk001Sub001Block120Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part005] using hcert

def TailChunk001Sub001Block120Part006SupportExplicit : Finset ℕ :=
  ([29662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part006 : ℚ :=
  (5498964025 : ℚ) / 48378394799421042

def SurrogateDiagonalTailChunk001Sub001Block120Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29662
    = surrogateDiagTailX0RatChunk001Sub001Block120Part006

theorem surrogateDiagonalTailChunk001Sub001Block120Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part006] using hcert

def TailChunk001Sub001Block120Part007SupportExplicit : Finset ℕ :=
  ([29663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part007 : ℚ :=
  (13748337015625 : ℚ) / 483914449109021591442

def SurrogateDiagonalTailChunk001Sub001Block120Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29663
    = surrogateDiagTailX0RatChunk001Sub001Block120Part007

theorem surrogateDiagonalTailChunk001Sub001Block120Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part007] using hcert

def TailChunk001Sub001Block120Part008SupportExplicit : Finset ℕ :=
  ([29665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part008 : ℚ :=
  (10449105412825 : ℚ) / 205089051183861989376

def SurrogateDiagonalTailChunk001Sub001Block120Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29665
    = surrogateDiagTailX0RatChunk001Sub001Block120Part008

theorem surrogateDiagonalTailChunk001Sub001Block120Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part008] using hcert

def TailChunk001Sub001Block120Part009SupportExplicit : Finset ℕ :=
  ([29666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part009 : ℚ :=
  (4608305093075 : ℚ) / 23141254954049224704

def SurrogateDiagonalTailChunk001Sub001Block120Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29666
    = surrogateDiagTailX0RatChunk001Sub001Block120Part009

theorem surrogateDiagonalTailChunk001Sub001Block120Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part009] using hcert

def TailChunk001Sub001Block120Part010SupportExplicit : Finset ℕ :=
  ([29667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part010 : ℚ :=
  (3803706043 : ℚ) / 41497577856000000

def SurrogateDiagonalTailChunk001Sub001Block120Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29667
    = surrogateDiagTailX0RatChunk001Sub001Block120Part010

theorem surrogateDiagonalTailChunk001Sub001Block120Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part010] using hcert

def TailChunk001Sub001Block120Part011SupportExplicit : Finset ℕ :=
  ([29669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part011 : ℚ :=
  (13753899390625 : ℚ) / 484306110869534506272

def SurrogateDiagonalTailChunk001Sub001Block120Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29669
    = surrogateDiagTailX0RatChunk001Sub001Block120Part011

theorem surrogateDiagonalTailChunk001Sub001Block120Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part011] using hcert

def TailChunk001Sub001Block120Part012SupportExplicit : Finset ℕ :=
  ([29670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part012 : ℚ :=
  (72802450025 : ℚ) / 138255027174899712

def SurrogateDiagonalTailChunk001Sub001Block120Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29670
    = surrogateDiagTailX0RatChunk001Sub001Block120Part012

theorem surrogateDiagonalTailChunk001Sub001Block120Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part012] using hcert

def TailChunk001Sub001Block120Part013SupportExplicit : Finset ℕ :=
  ([29671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part013 : ℚ :=
  (22009206025 : ℚ) / 775098748171093842

def SurrogateDiagonalTailChunk001Sub001Block120Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29671
    = surrogateDiagTailX0RatChunk001Sub001Block120Part013

theorem surrogateDiagonalTailChunk001Sub001Block120Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part013] using hcert

def TailChunk001Sub001Block120Part014SupportExplicit : Finset ℕ :=
  ([29674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part014 : ℚ :=
  (58189406201 : ℚ) / 477852991488000000

def SurrogateDiagonalTailChunk001Sub001Block120Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29674
    = surrogateDiagTailX0RatChunk001Sub001Block120Part014

theorem surrogateDiagonalTailChunk001Sub001Block120Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part014] using hcert

def TailChunk001Sub001Block120Part015SupportExplicit : Finset ℕ :=
  ([29677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part015 : ℚ :=
  (26565269290475 : ℚ) / 898511636670305169984

def SurrogateDiagonalTailChunk001Sub001Block120Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29677
    = surrogateDiagTailX0RatChunk001Sub001Block120Part015

theorem surrogateDiagonalTailChunk001Sub001Block120Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part015] using hcert

def TailChunk001Sub001Block120Part016SupportExplicit : Finset ℕ :=
  ([29678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part016 : ℚ :=
  (417886933633 : ℚ) / 2520977854752000000

def SurrogateDiagonalTailChunk001Sub001Block120Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29678
    = surrogateDiagTailX0RatChunk001Sub001Block120Part016

theorem surrogateDiagonalTailChunk001Sub001Block120Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part016] using hcert

def TailChunk001Sub001Block120Part017SupportExplicit : Finset ℕ :=
  ([29679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part017 : ℚ :=
  (105445897649 : ℚ) / 1383872882304614400

def SurrogateDiagonalTailChunk001Sub001Block120Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29679
    = surrogateDiagTailX0RatChunk001Sub001Block120Part017

theorem surrogateDiagonalTailChunk001Sub001Block120Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part017] using hcert

def TailChunk001Sub001Block120Part018SupportExplicit : Finset ℕ :=
  ([29681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part018 : ℚ :=
  (26666696623925 : ℚ) / 905444182624976115264

def SurrogateDiagonalTailChunk001Sub001Block120Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29681
    = surrogateDiagTailX0RatChunk001Sub001Block120Part018

theorem surrogateDiagonalTailChunk001Sub001Block120Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part018] using hcert

def TailChunk001Sub001Block120Part019SupportExplicit : Finset ℕ :=
  ([29683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part019 : ℚ :=
  (13766882640625 : ℚ) / 485220912861506387922

def SurrogateDiagonalTailChunk001Sub001Block120Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29683
    = surrogateDiagTailX0RatChunk001Sub001Block120Part019

theorem surrogateDiagonalTailChunk001Sub001Block120Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part019] using hcert

def TailChunk001Sub001Block120Part020SupportExplicit : Finset ℕ :=
  ([29685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part020 : ℚ :=
  (1344985024875 : ℚ) / 13065038981517697024

def SurrogateDiagonalTailChunk001Sub001Block120Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29685
    = surrogateDiagTailX0RatChunk001Sub001Block120Part020

theorem surrogateDiagonalTailChunk001Sub001Block120Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part020] using hcert

def TailChunk001Sub001Block120Part021SupportExplicit : Finset ℕ :=
  ([29686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part021 : ℚ :=
  (3442416390625 : ℚ) / 30334481535971370162

def SurrogateDiagonalTailChunk001Sub001Block120Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29686
    = surrogateDiagTailX0RatChunk001Sub001Block120Part021

theorem surrogateDiagonalTailChunk001Sub001Block120Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part021] using hcert

def TailChunk001Sub001Block120Part022SupportExplicit : Finset ℕ :=
  ([29687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part022 : ℚ :=
  (332622119189 : ℚ) / 8378866555842723840

def SurrogateDiagonalTailChunk001Sub001Block120Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29687
    = surrogateDiagTailX0RatChunk001Sub001Block120Part022

theorem surrogateDiagonalTailChunk001Sub001Block120Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part022] using hcert

def TailChunk001Sub001Block120Part023SupportExplicit : Finset ℕ :=
  ([29689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part023 : ℚ :=
  (183819656809 : ℚ) / 5299740823579072320

def SurrogateDiagonalTailChunk001Sub001Block120Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29689
    = surrogateDiagTailX0RatChunk001Sub001Block120Part023

theorem surrogateDiagonalTailChunk001Sub001Block120Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part023] using hcert

def TailChunk001Sub001Block120Part024SupportExplicit : Finset ℕ :=
  ([29690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block120Part024 : ℚ :=
  (9361719312475 : ℚ) / 49673231112539209728

def SurrogateDiagonalTailChunk001Sub001Block120Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29690
    = surrogateDiagTailX0RatChunk001Sub001Block120Part024

theorem surrogateDiagonalTailChunk001Sub001Block120Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block120Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block120Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block120Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block120Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block120Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block120HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block120Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block120Part000
    + surrogateDiagTailX0RatChunk001Sub001Block120Part001
    + surrogateDiagTailX0RatChunk001Sub001Block120Part002
    + surrogateDiagTailX0RatChunk001Sub001Block120Part003
    + surrogateDiagTailX0RatChunk001Sub001Block120Part004
    + surrogateDiagTailX0RatChunk001Sub001Block120Part005
    + surrogateDiagTailX0RatChunk001Sub001Block120Part006
    + surrogateDiagTailX0RatChunk001Sub001Block120Part007
    + surrogateDiagTailX0RatChunk001Sub001Block120Part008
    + surrogateDiagTailX0RatChunk001Sub001Block120Part009

def surrogateDiagonalTailChunk001Sub001Block120MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block120Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block120Part010
    + surrogateDiagTailX0RatChunk001Sub001Block120Part011
    + surrogateDiagTailX0RatChunk001Sub001Block120Part012
    + surrogateDiagTailX0RatChunk001Sub001Block120Part013
    + surrogateDiagTailX0RatChunk001Sub001Block120Part014
    + surrogateDiagTailX0RatChunk001Sub001Block120Part015
    + surrogateDiagTailX0RatChunk001Sub001Block120Part016
    + surrogateDiagTailX0RatChunk001Sub001Block120Part017
    + surrogateDiagTailX0RatChunk001Sub001Block120Part018
    + surrogateDiagTailX0RatChunk001Sub001Block120Part019

def surrogateDiagonalTailChunk001Sub001Block120TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block120Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block120Part020
    + surrogateDiagTailX0RatChunk001Sub001Block120Part021
    + surrogateDiagTailX0RatChunk001Sub001Block120Part022
    + surrogateDiagTailX0RatChunk001Sub001Block120Part023
    + surrogateDiagTailX0RatChunk001Sub001Block120Part024

def surrogateDiagonalTailChunk001Sub001Block120Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block120HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block120MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block120TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block120 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block120Part000
    + surrogateDiagTailX0RatChunk001Sub001Block120Part001
    + surrogateDiagTailX0RatChunk001Sub001Block120Part002
    + surrogateDiagTailX0RatChunk001Sub001Block120Part003
    + surrogateDiagTailX0RatChunk001Sub001Block120Part004
    + surrogateDiagTailX0RatChunk001Sub001Block120Part005
    + surrogateDiagTailX0RatChunk001Sub001Block120Part006
    + surrogateDiagTailX0RatChunk001Sub001Block120Part007
    + surrogateDiagTailX0RatChunk001Sub001Block120Part008
    + surrogateDiagTailX0RatChunk001Sub001Block120Part009
    + surrogateDiagTailX0RatChunk001Sub001Block120Part010
    + surrogateDiagTailX0RatChunk001Sub001Block120Part011
    + surrogateDiagTailX0RatChunk001Sub001Block120Part012
    + surrogateDiagTailX0RatChunk001Sub001Block120Part013
    + surrogateDiagTailX0RatChunk001Sub001Block120Part014
    + surrogateDiagTailX0RatChunk001Sub001Block120Part015
    + surrogateDiagTailX0RatChunk001Sub001Block120Part016
    + surrogateDiagTailX0RatChunk001Sub001Block120Part017
    + surrogateDiagTailX0RatChunk001Sub001Block120Part018
    + surrogateDiagTailX0RatChunk001Sub001Block120Part019
    + surrogateDiagTailX0RatChunk001Sub001Block120Part020
    + surrogateDiagTailX0RatChunk001Sub001Block120Part021
    + surrogateDiagTailX0RatChunk001Sub001Block120Part022
    + surrogateDiagTailX0RatChunk001Sub001Block120Part023
    + surrogateDiagTailX0RatChunk001Sub001Block120Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block120_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block120Head + surrogateDiagTailX0RatChunk001Sub001Block120Mid + surrogateDiagTailX0RatChunk001Sub001Block120Tail =
      surrogateDiagTailX0RatChunk001Sub001Block120 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block120Head surrogateDiagTailX0RatChunk001Sub001Block120Mid surrogateDiagTailX0RatChunk001Sub001Block120Tail surrogateDiagTailX0RatChunk001Sub001Block120
  ring

def SurrogateDiagonalTailChunk001Sub001Block120HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block120HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block120Head

def SurrogateDiagonalTailChunk001Sub001Block120MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block120MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block120Mid

def SurrogateDiagonalTailChunk001Sub001Block120TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block120TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block120Tail

theorem surrogateDiagonalTailChunk001Sub001Block120_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block120HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block120MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block120TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block120Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block120 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block120HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block120MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block120TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block120Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block120_eq_head_add_mid_add_tail

/-- Block 121 covers tail-support indices [18025,18050) and q from 29693 to 29731. -/

def TailChunk001Sub001Block121Part000SupportExplicit : Finset ℕ :=
  ([29693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part000 : ℚ :=
  (506604811063 : ℚ) / 16220955145204576800

def SurrogateDiagonalTailChunk001Sub001Block121Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29693
    = surrogateDiagTailX0RatChunk001Sub001Block121Part000

theorem surrogateDiagonalTailChunk001Sub001Block121Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part000] using hcert

def TailChunk001Sub001Block121Part001SupportExplicit : Finset ℕ :=
  ([29695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part001 : ℚ :=
  (2203818390625 : ℚ) / 49740210008964674688

def SurrogateDiagonalTailChunk001Sub001Block121Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29695
    = surrogateDiagTailX0RatChunk001Sub001Block121Part001

theorem surrogateDiagonalTailChunk001Sub001Block121Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part001] using hcert

def TailChunk001Sub001Block121Part002SupportExplicit : Finset ℕ :=
  ([29697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part002 : ℚ :=
  (88871347717 : ℚ) / 1228316336089989120

def SurrogateDiagonalTailChunk001Sub001Block121Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29697
    = surrogateDiagTailX0RatChunk001Sub001Block121Part002

theorem surrogateDiagonalTailChunk001Sub001Block121Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part002] using hcert

def TailChunk001Sub001Block121Part003SupportExplicit : Finset ℕ :=
  ([29698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part003 : ℚ :=
  (104046245117 : ℚ) / 845889143747149440

def SurrogateDiagonalTailChunk001Sub001Block121Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29698
    = surrogateDiagTailX0RatChunk001Sub001Block121Part003

theorem surrogateDiagonalTailChunk001Sub001Block121Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part003] using hcert

def TailChunk001Sub001Block121Part004SupportExplicit : Finset ℕ :=
  ([29699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part004 : ℚ :=
  (12291163941625 : ℚ) / 380735835841185841152

def SurrogateDiagonalTailChunk001Sub001Block121Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29699
    = surrogateDiagTailX0RatChunk001Sub001Block121Part004

theorem surrogateDiagonalTailChunk001Sub001Block121Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part004] using hcert

def TailChunk001Sub001Block121Part005SupportExplicit : Finset ℕ :=
  ([29701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part005 : ℚ :=
  (41616996691225 : ℚ) / 1049335865910451502208

def SurrogateDiagonalTailChunk001Sub001Block121Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29701
    = surrogateDiagTailX0RatChunk001Sub001Block121Part005

theorem surrogateDiagonalTailChunk001Sub001Block121Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part005] using hcert

def TailChunk001Sub001Block121Part006SupportExplicit : Finset ℕ :=
  ([29702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part006 : ℚ :=
  (220552201 : ℚ) / 1945595961634050

def SurrogateDiagonalTailChunk001Sub001Block121Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29702
    = surrogateDiagTailX0RatChunk001Sub001Block121Part006

theorem surrogateDiagonalTailChunk001Sub001Block121Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part006] using hcert

def TailChunk001Sub001Block121Part007SupportExplicit : Finset ℕ :=
  ([29703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part007 : ℚ :=
  (89102269127 : ℚ) / 1397510006112000000

def SurrogateDiagonalTailChunk001Sub001Block121Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29703
    = surrogateDiagTailX0RatChunk001Sub001Block121Part007

theorem surrogateDiagonalTailChunk001Sub001Block121Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part007] using hcert

def TailChunk001Sub001Block121Part008SupportExplicit : Finset ℕ :=
  ([29705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part008 : ℚ :=
  (15238785351725 : ℚ) / 286959880874684841984

def SurrogateDiagonalTailChunk001Sub001Block121Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29705
    = surrogateDiagTailX0RatChunk001Sub001Block121Part008

theorem surrogateDiagonalTailChunk001Sub001Block121Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part008] using hcert

def TailChunk001Sub001Block121Part009SupportExplicit : Finset ℕ :=
  ([29706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part009 : ℚ :=
  (1225625051 : ℚ) / 19215762584040000

def SurrogateDiagonalTailChunk001Sub001Block121Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29706
    = surrogateDiagTailX0RatChunk001Sub001Block121Part009

theorem surrogateDiagonalTailChunk001Sub001Block121Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part009] using hcert

def TailChunk001Sub001Block121Part010SupportExplicit : Finset ℕ :=
  ([29707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part010 : ℚ :=
  (3322320107 : ℚ) / 36158210865701913600

def SurrogateDiagonalTailChunk001Sub001Block121Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29707
    = surrogateDiagTailX0RatChunk001Sub001Block121Part010

theorem surrogateDiagonalTailChunk001Sub001Block121Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part010] using hcert

def TailChunk001Sub001Block121Part011SupportExplicit : Finset ℕ :=
  ([29710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part011 : ℚ :=
  (4420456529 : ℚ) / 398458052942653440

def SurrogateDiagonalTailChunk001Sub001Block121Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29710
    = surrogateDiagTailX0RatChunk001Sub001Block121Part011

theorem surrogateDiagonalTailChunk001Sub001Block121Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part011] using hcert

def TailChunk001Sub001Block121Part012SupportExplicit : Finset ℕ :=
  ([29711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part012 : ℚ :=
  (29769131431 : ℚ) / 45146786070999859200

def SurrogateDiagonalTailChunk001Sub001Block121Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29711
    = surrogateDiagTailX0RatChunk001Sub001Block121Part012

theorem surrogateDiagonalTailChunk001Sub001Block121Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part012] using hcert

def TailChunk001Sub001Block121Part013SupportExplicit : Finset ℕ :=
  ([29713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part013 : ℚ :=
  (4424920319 : ℚ) / 35273648192582721600

def SurrogateDiagonalTailChunk001Sub001Block121Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29713
    = surrogateDiagTailX0RatChunk001Sub001Block121Part013

theorem surrogateDiagonalTailChunk001Sub001Block121Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part013] using hcert

def TailChunk001Sub001Block121Part014SupportExplicit : Finset ℕ :=
  ([29714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part014 : ℚ :=
  (20168470075 : ℚ) / 28372805853749612832

def SurrogateDiagonalTailChunk001Sub001Block121Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29714
    = surrogateDiagTailX0RatChunk001Sub001Block121Part014

theorem surrogateDiagonalTailChunk001Sub001Block121Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part014] using hcert

def TailChunk001Sub001Block121Part015SupportExplicit : Finset ℕ :=
  ([29715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part015 : ℚ :=
  (494601932975 : ℚ) / 41971862940428795904

def SurrogateDiagonalTailChunk001Sub001Block121Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29715
    = surrogateDiagTailX0RatChunk001Sub001Block121Part015

theorem surrogateDiagonalTailChunk001Sub001Block121Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part015] using hcert

def TailChunk001Sub001Block121Part016SupportExplicit : Finset ℕ :=
  ([29717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block121Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29717
    = surrogateDiagTailX0RatChunk001Sub001Block121Part016

theorem surrogateDiagonalTailChunk001Sub001Block121Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part016] using hcert

def TailChunk001Sub001Block121Part017SupportExplicit : Finset ℕ :=
  ([29719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part017 : ℚ :=
  (8343144725 : ℚ) / 132426859279260844032

def SurrogateDiagonalTailChunk001Sub001Block121Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29719
    = surrogateDiagTailX0RatChunk001Sub001Block121Part017

theorem surrogateDiagonalTailChunk001Sub001Block121Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part017] using hcert

def TailChunk001Sub001Block121Part018SupportExplicit : Finset ℕ :=
  ([29721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part018 : ℚ :=
  (41675 : ℚ) / 25678049212573056

def SurrogateDiagonalTailChunk001Sub001Block121Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29721
    = surrogateDiagTailX0RatChunk001Sub001Block121Part018

theorem surrogateDiagonalTailChunk001Sub001Block121Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part018] using hcert

def TailChunk001Sub001Block121Part019SupportExplicit : Finset ℕ :=
  ([29722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part019 : ℚ :=
  (15535645883 : ℚ) / 880778633910681600

def SurrogateDiagonalTailChunk001Sub001Block121Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29722
    = surrogateDiagTailX0RatChunk001Sub001Block121Part019

theorem surrogateDiagonalTailChunk001Sub001Block121Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part019] using hcert

def TailChunk001Sub001Block121Part020SupportExplicit : Finset ℕ :=
  ([29723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block121Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29723
    = surrogateDiagTailX0RatChunk001Sub001Block121Part020

theorem surrogateDiagonalTailChunk001Sub001Block121Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part020] using hcert

def TailChunk001Sub001Block121Part021SupportExplicit : Finset ℕ :=
  ([29726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part021 : ℚ :=
  (77554040275 : ℚ) / 113864908016279912448

def SurrogateDiagonalTailChunk001Sub001Block121Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29726
    = surrogateDiagTailX0RatChunk001Sub001Block121Part021

theorem surrogateDiagonalTailChunk001Sub001Block121Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part021] using hcert

def TailChunk001Sub001Block121Part022SupportExplicit : Finset ℕ :=
  ([29729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part022 : ℚ :=
  (53618743897 : ℚ) / 35919683731862323200

def SurrogateDiagonalTailChunk001Sub001Block121Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29729
    = surrogateDiagTailX0RatChunk001Sub001Block121Part022

theorem surrogateDiagonalTailChunk001Sub001Block121Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part022] using hcert

def TailChunk001Sub001Block121Part023SupportExplicit : Finset ℕ :=
  ([29730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part023 : ℚ :=
  (11292519791 : ℚ) / 78707763544227840

def SurrogateDiagonalTailChunk001Sub001Block121Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29730
    = surrogateDiagTailX0RatChunk001Sub001Block121Part023

theorem surrogateDiagonalTailChunk001Sub001Block121Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part023] using hcert

def TailChunk001Sub001Block121Part024SupportExplicit : Finset ℕ :=
  ([29731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block121Part024 : ℚ :=
  (24327677575 : ℚ) / 52443658794974828544

def SurrogateDiagonalTailChunk001Sub001Block121Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29731
    = surrogateDiagTailX0RatChunk001Sub001Block121Part024

theorem surrogateDiagonalTailChunk001Sub001Block121Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block121Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block121Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block121Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block121Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block121Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block121HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block121Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block121Part000
    + surrogateDiagTailX0RatChunk001Sub001Block121Part001
    + surrogateDiagTailX0RatChunk001Sub001Block121Part002
    + surrogateDiagTailX0RatChunk001Sub001Block121Part003
    + surrogateDiagTailX0RatChunk001Sub001Block121Part004
    + surrogateDiagTailX0RatChunk001Sub001Block121Part005
    + surrogateDiagTailX0RatChunk001Sub001Block121Part006
    + surrogateDiagTailX0RatChunk001Sub001Block121Part007
    + surrogateDiagTailX0RatChunk001Sub001Block121Part008
    + surrogateDiagTailX0RatChunk001Sub001Block121Part009

def surrogateDiagonalTailChunk001Sub001Block121MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block121Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block121Part010
    + surrogateDiagTailX0RatChunk001Sub001Block121Part011
    + surrogateDiagTailX0RatChunk001Sub001Block121Part012
    + surrogateDiagTailX0RatChunk001Sub001Block121Part013
    + surrogateDiagTailX0RatChunk001Sub001Block121Part014
    + surrogateDiagTailX0RatChunk001Sub001Block121Part015
    + surrogateDiagTailX0RatChunk001Sub001Block121Part016
    + surrogateDiagTailX0RatChunk001Sub001Block121Part017
    + surrogateDiagTailX0RatChunk001Sub001Block121Part018
    + surrogateDiagTailX0RatChunk001Sub001Block121Part019

def surrogateDiagonalTailChunk001Sub001Block121TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block121Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block121Part020
    + surrogateDiagTailX0RatChunk001Sub001Block121Part021
    + surrogateDiagTailX0RatChunk001Sub001Block121Part022
    + surrogateDiagTailX0RatChunk001Sub001Block121Part023
    + surrogateDiagTailX0RatChunk001Sub001Block121Part024

def surrogateDiagonalTailChunk001Sub001Block121Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block121HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block121MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block121TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block121 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block121Part000
    + surrogateDiagTailX0RatChunk001Sub001Block121Part001
    + surrogateDiagTailX0RatChunk001Sub001Block121Part002
    + surrogateDiagTailX0RatChunk001Sub001Block121Part003
    + surrogateDiagTailX0RatChunk001Sub001Block121Part004
    + surrogateDiagTailX0RatChunk001Sub001Block121Part005
    + surrogateDiagTailX0RatChunk001Sub001Block121Part006
    + surrogateDiagTailX0RatChunk001Sub001Block121Part007
    + surrogateDiagTailX0RatChunk001Sub001Block121Part008
    + surrogateDiagTailX0RatChunk001Sub001Block121Part009
    + surrogateDiagTailX0RatChunk001Sub001Block121Part010
    + surrogateDiagTailX0RatChunk001Sub001Block121Part011
    + surrogateDiagTailX0RatChunk001Sub001Block121Part012
    + surrogateDiagTailX0RatChunk001Sub001Block121Part013
    + surrogateDiagTailX0RatChunk001Sub001Block121Part014
    + surrogateDiagTailX0RatChunk001Sub001Block121Part015
    + surrogateDiagTailX0RatChunk001Sub001Block121Part016
    + surrogateDiagTailX0RatChunk001Sub001Block121Part017
    + surrogateDiagTailX0RatChunk001Sub001Block121Part018
    + surrogateDiagTailX0RatChunk001Sub001Block121Part019
    + surrogateDiagTailX0RatChunk001Sub001Block121Part020
    + surrogateDiagTailX0RatChunk001Sub001Block121Part021
    + surrogateDiagTailX0RatChunk001Sub001Block121Part022
    + surrogateDiagTailX0RatChunk001Sub001Block121Part023
    + surrogateDiagTailX0RatChunk001Sub001Block121Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block121_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block121Head + surrogateDiagTailX0RatChunk001Sub001Block121Mid + surrogateDiagTailX0RatChunk001Sub001Block121Tail =
      surrogateDiagTailX0RatChunk001Sub001Block121 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block121Head surrogateDiagTailX0RatChunk001Sub001Block121Mid surrogateDiagTailX0RatChunk001Sub001Block121Tail surrogateDiagTailX0RatChunk001Sub001Block121
  ring

def SurrogateDiagonalTailChunk001Sub001Block121HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block121HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block121Head

def SurrogateDiagonalTailChunk001Sub001Block121MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block121MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block121Mid

def SurrogateDiagonalTailChunk001Sub001Block121TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block121TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block121Tail

theorem surrogateDiagonalTailChunk001Sub001Block121_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block121HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block121MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block121TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block121Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block121 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block121HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block121MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block121TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block121Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block121_eq_head_add_mid_add_tail

/-- Block 122 covers tail-support indices [18050,18075) and q from 29733 to 29774. -/

def TailChunk001Sub001Block122Part000SupportExplicit : Finset ℕ :=
  ([29733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part000 : ℚ :=
  (9512876683 : ℚ) / 1917079603956940800

def SurrogateDiagonalTailChunk001Sub001Block122Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29733
    = surrogateDiagTailX0RatChunk001Sub001Block122Part000

theorem surrogateDiagonalTailChunk001Sub001Block122Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part000] using hcert

def TailChunk001Sub001Block122Part001SupportExplicit : Finset ℕ :=
  ([29734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29734
    = surrogateDiagTailX0RatChunk001Sub001Block122Part001

theorem surrogateDiagonalTailChunk001Sub001Block122Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part001] using hcert

def TailChunk001Sub001Block122Part002SupportExplicit : Finset ℕ :=
  ([29735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part002 : ℚ :=
  (98375921725 : ℚ) / 159189797157262589952

def SurrogateDiagonalTailChunk001Sub001Block122Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29735
    = surrogateDiagTailX0RatChunk001Sub001Block122Part002

theorem surrogateDiagonalTailChunk001Sub001Block122Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part002] using hcert

def TailChunk001Sub001Block122Part003SupportExplicit : Finset ℕ :=
  ([29737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part003 : ℚ :=
  (735927081 : ℚ) / 12420605431084011200

def SurrogateDiagonalTailChunk001Sub001Block122Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29737
    = surrogateDiagTailX0RatChunk001Sub001Block122Part003

theorem surrogateDiagonalTailChunk001Sub001Block122Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part003] using hcert

def TailChunk001Sub001Block122Part004SupportExplicit : Finset ℕ :=
  ([29738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29738
    = surrogateDiagTailX0RatChunk001Sub001Block122Part004

theorem surrogateDiagonalTailChunk001Sub001Block122Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part004] using hcert

def TailChunk001Sub001Block122Part005SupportExplicit : Finset ℕ :=
  ([29739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part005 : ℚ :=
  (3727232559 : ℚ) / 4272185717255526400

def SurrogateDiagonalTailChunk001Sub001Block122Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29739
    = surrogateDiagTailX0RatChunk001Sub001Block122Part005

theorem surrogateDiagonalTailChunk001Sub001Block122Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part005] using hcert

def TailChunk001Sub001Block122Part006SupportExplicit : Finset ℕ :=
  ([29741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29741
    = surrogateDiagTailX0RatChunk001Sub001Block122Part006

theorem surrogateDiagonalTailChunk001Sub001Block122Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part006] using hcert

def TailChunk001Sub001Block122Part007SupportExplicit : Finset ℕ :=
  ([29742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part007 : ℚ :=
  (1958859775 : ℚ) / 30786191724903552

def SurrogateDiagonalTailChunk001Sub001Block122Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29742
    = surrogateDiagTailX0RatChunk001Sub001Block122Part007

theorem surrogateDiagonalTailChunk001Sub001Block122Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part007] using hcert

def TailChunk001Sub001Block122Part008SupportExplicit : Finset ℕ :=
  ([29746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part008 : ℚ :=
  (75860844625 : ℚ) / 114489765422538265728

def SurrogateDiagonalTailChunk001Sub001Block122Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29746
    = surrogateDiagTailX0RatChunk001Sub001Block122Part008

theorem surrogateDiagonalTailChunk001Sub001Block122Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part008] using hcert

def TailChunk001Sub001Block122Part009SupportExplicit : Finset ℕ :=
  ([29747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part009 : ℚ :=
  (4258422097 : ℚ) / 74726763324192000000

def SurrogateDiagonalTailChunk001Sub001Block122Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29747
    = surrogateDiagTailX0RatChunk001Sub001Block122Part009

theorem surrogateDiagonalTailChunk001Sub001Block122Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part009] using hcert

def TailChunk001Sub001Block122Part010SupportExplicit : Finset ℕ :=
  ([29749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part010 : ℚ :=
  (6100254799 : ℚ) / 73313531072835715200

def SurrogateDiagonalTailChunk001Sub001Block122Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29749
    = surrogateDiagTailX0RatChunk001Sub001Block122Part010

theorem surrogateDiagonalTailChunk001Sub001Block122Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part010] using hcert

def TailChunk001Sub001Block122Part011SupportExplicit : Finset ℕ :=
  ([29751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part011 : ℚ :=
  (1286766581 : ℚ) / 2787053684352215040

def SurrogateDiagonalTailChunk001Sub001Block122Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29751
    = surrogateDiagTailX0RatChunk001Sub001Block122Part011

theorem surrogateDiagonalTailChunk001Sub001Block122Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part011] using hcert

def TailChunk001Sub001Block122Part012SupportExplicit : Finset ℕ :=
  ([29753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29753
    = surrogateDiagTailX0RatChunk001Sub001Block122Part012

theorem surrogateDiagonalTailChunk001Sub001Block122Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part012] using hcert

def TailChunk001Sub001Block122Part013SupportExplicit : Finset ℕ :=
  ([29755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part013 : ℚ :=
  (535871011 : ℚ) / 403188461568000000

def SurrogateDiagonalTailChunk001Sub001Block122Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29755
    = surrogateDiagTailX0RatChunk001Sub001Block122Part013

theorem surrogateDiagonalTailChunk001Sub001Block122Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part013] using hcert

def TailChunk001Sub001Block122Part014SupportExplicit : Finset ℕ :=
  ([29757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part014 : ℚ :=
  (127453026325 : ℚ) / 16252842985559949312

def SurrogateDiagonalTailChunk001Sub001Block122Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29757
    = surrogateDiagTailX0RatChunk001Sub001Block122Part014

theorem surrogateDiagonalTailChunk001Sub001Block122Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part014] using hcert

def TailChunk001Sub001Block122Part015SupportExplicit : Finset ℕ :=
  ([29758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29758
    = surrogateDiagTailX0RatChunk001Sub001Block122Part015

theorem surrogateDiagonalTailChunk001Sub001Block122Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part015] using hcert

def TailChunk001Sub001Block122Part016SupportExplicit : Finset ℕ :=
  ([29759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29759
    = surrogateDiagTailX0RatChunk001Sub001Block122Part016

theorem surrogateDiagonalTailChunk001Sub001Block122Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part016] using hcert

def TailChunk001Sub001Block122Part017SupportExplicit : Finset ℕ :=
  ([29761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29761
    = surrogateDiagTailX0RatChunk001Sub001Block122Part017

theorem surrogateDiagonalTailChunk001Sub001Block122Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part017] using hcert

def TailChunk001Sub001Block122Part018SupportExplicit : Finset ℕ :=
  ([29762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part018 : ℚ :=
  (17935854975 : ℚ) / 8500929374891450464

def SurrogateDiagonalTailChunk001Sub001Block122Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29762
    = surrogateDiagTailX0RatChunk001Sub001Block122Part018

theorem surrogateDiagonalTailChunk001Sub001Block122Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part018] using hcert

def TailChunk001Sub001Block122Part019SupportExplicit : Finset ℕ :=
  ([29765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part019 : ℚ :=
  (2215394443375 : ℚ) / 803375372610199093248

def SurrogateDiagonalTailChunk001Sub001Block122Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29765
    = surrogateDiagTailX0RatChunk001Sub001Block122Part019

theorem surrogateDiagonalTailChunk001Sub001Block122Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part019] using hcert

def TailChunk001Sub001Block122Part020SupportExplicit : Finset ℕ :=
  ([29769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part020 : ℚ :=
  (125025 : ℚ) / 77533051639480448

def SurrogateDiagonalTailChunk001Sub001Block122Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29769
    = surrogateDiagTailX0RatChunk001Sub001Block122Part020

theorem surrogateDiagonalTailChunk001Sub001Block122Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part020] using hcert

def TailChunk001Sub001Block122Part021SupportExplicit : Finset ℕ :=
  ([29770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part021 : ℚ :=
  (629529530975 : ℚ) / 17934992554667802624

def SurrogateDiagonalTailChunk001Sub001Block122Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29770
    = surrogateDiagTailX0RatChunk001Sub001Block122Part021

theorem surrogateDiagonalTailChunk001Sub001Block122Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part021] using hcert

def TailChunk001Sub001Block122Part022SupportExplicit : Finset ℕ :=
  ([29771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part022 : ℚ :=
  (1131843962425 : ℚ) / 1059265636995937978368

def SurrogateDiagonalTailChunk001Sub001Block122Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29771
    = surrogateDiagTailX0RatChunk001Sub001Block122Part022

theorem surrogateDiagonalTailChunk001Sub001Block122Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part022] using hcert

def TailChunk001Sub001Block122Part023SupportExplicit : Finset ℕ :=
  ([29773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part023 : ℚ :=
  (465255752575 : ℚ) / 1578642934524970071168

def SurrogateDiagonalTailChunk001Sub001Block122Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29773
    = surrogateDiagTailX0RatChunk001Sub001Block122Part023

theorem surrogateDiagonalTailChunk001Sub001Block122Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part023] using hcert

def TailChunk001Sub001Block122Part024SupportExplicit : Finset ℕ :=
  ([29774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block122Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block122Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29774
    = surrogateDiagTailX0RatChunk001Sub001Block122Part024

theorem surrogateDiagonalTailChunk001Sub001Block122Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block122Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block122Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block122Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block122Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block122Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block122HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block122Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block122Part000
    + surrogateDiagTailX0RatChunk001Sub001Block122Part001
    + surrogateDiagTailX0RatChunk001Sub001Block122Part002
    + surrogateDiagTailX0RatChunk001Sub001Block122Part003
    + surrogateDiagTailX0RatChunk001Sub001Block122Part004
    + surrogateDiagTailX0RatChunk001Sub001Block122Part005
    + surrogateDiagTailX0RatChunk001Sub001Block122Part006
    + surrogateDiagTailX0RatChunk001Sub001Block122Part007
    + surrogateDiagTailX0RatChunk001Sub001Block122Part008
    + surrogateDiagTailX0RatChunk001Sub001Block122Part009

def surrogateDiagonalTailChunk001Sub001Block122MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block122Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block122Part010
    + surrogateDiagTailX0RatChunk001Sub001Block122Part011
    + surrogateDiagTailX0RatChunk001Sub001Block122Part012
    + surrogateDiagTailX0RatChunk001Sub001Block122Part013
    + surrogateDiagTailX0RatChunk001Sub001Block122Part014
    + surrogateDiagTailX0RatChunk001Sub001Block122Part015
    + surrogateDiagTailX0RatChunk001Sub001Block122Part016
    + surrogateDiagTailX0RatChunk001Sub001Block122Part017
    + surrogateDiagTailX0RatChunk001Sub001Block122Part018
    + surrogateDiagTailX0RatChunk001Sub001Block122Part019

def surrogateDiagonalTailChunk001Sub001Block122TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block122Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block122Part020
    + surrogateDiagTailX0RatChunk001Sub001Block122Part021
    + surrogateDiagTailX0RatChunk001Sub001Block122Part022
    + surrogateDiagTailX0RatChunk001Sub001Block122Part023
    + surrogateDiagTailX0RatChunk001Sub001Block122Part024

def surrogateDiagonalTailChunk001Sub001Block122Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block122HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block122MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block122TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block122 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block122Part000
    + surrogateDiagTailX0RatChunk001Sub001Block122Part001
    + surrogateDiagTailX0RatChunk001Sub001Block122Part002
    + surrogateDiagTailX0RatChunk001Sub001Block122Part003
    + surrogateDiagTailX0RatChunk001Sub001Block122Part004
    + surrogateDiagTailX0RatChunk001Sub001Block122Part005
    + surrogateDiagTailX0RatChunk001Sub001Block122Part006
    + surrogateDiagTailX0RatChunk001Sub001Block122Part007
    + surrogateDiagTailX0RatChunk001Sub001Block122Part008
    + surrogateDiagTailX0RatChunk001Sub001Block122Part009
    + surrogateDiagTailX0RatChunk001Sub001Block122Part010
    + surrogateDiagTailX0RatChunk001Sub001Block122Part011
    + surrogateDiagTailX0RatChunk001Sub001Block122Part012
    + surrogateDiagTailX0RatChunk001Sub001Block122Part013
    + surrogateDiagTailX0RatChunk001Sub001Block122Part014
    + surrogateDiagTailX0RatChunk001Sub001Block122Part015
    + surrogateDiagTailX0RatChunk001Sub001Block122Part016
    + surrogateDiagTailX0RatChunk001Sub001Block122Part017
    + surrogateDiagTailX0RatChunk001Sub001Block122Part018
    + surrogateDiagTailX0RatChunk001Sub001Block122Part019
    + surrogateDiagTailX0RatChunk001Sub001Block122Part020
    + surrogateDiagTailX0RatChunk001Sub001Block122Part021
    + surrogateDiagTailX0RatChunk001Sub001Block122Part022
    + surrogateDiagTailX0RatChunk001Sub001Block122Part023
    + surrogateDiagTailX0RatChunk001Sub001Block122Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block122_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block122Head + surrogateDiagTailX0RatChunk001Sub001Block122Mid + surrogateDiagTailX0RatChunk001Sub001Block122Tail =
      surrogateDiagTailX0RatChunk001Sub001Block122 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block122Head surrogateDiagTailX0RatChunk001Sub001Block122Mid surrogateDiagTailX0RatChunk001Sub001Block122Tail surrogateDiagTailX0RatChunk001Sub001Block122
  ring

def SurrogateDiagonalTailChunk001Sub001Block122HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block122HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block122Head

def SurrogateDiagonalTailChunk001Sub001Block122MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block122MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block122Mid

def SurrogateDiagonalTailChunk001Sub001Block122TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block122TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block122Tail

theorem surrogateDiagonalTailChunk001Sub001Block122_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block122HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block122MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block122TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block122Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block122 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block122HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block122MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block122TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block122Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block122_eq_head_add_mid_add_tail

/-- Block 123 covers tail-support indices [18075,18100) and q from 29777 to 29814. -/

def TailChunk001Sub001Block123Part000SupportExplicit : Finset ℕ :=
  ([29777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part000 : ℚ :=
  (382603751 : ℚ) / 558633256123862700

def SurrogateDiagonalTailChunk001Sub001Block123Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29777
    = surrogateDiagTailX0RatChunk001Sub001Block123Part000

theorem surrogateDiagonalTailChunk001Sub001Block123Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part000] using hcert

def TailChunk001Sub001Block123Part001SupportExplicit : Finset ℕ :=
  ([29778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part001 : ℚ :=
  (167512575125 : ℚ) / 1447579300697505792

def SurrogateDiagonalTailChunk001Sub001Block123Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29778
    = surrogateDiagTailX0RatChunk001Sub001Block123Part001

theorem surrogateDiagonalTailChunk001Sub001Block123Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part001] using hcert

def TailChunk001Sub001Block123Part002SupportExplicit : Finset ℕ :=
  ([29779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part002 : ℚ :=
  (61807095725 : ℚ) / 931038202329871417344

def SurrogateDiagonalTailChunk001Sub001Block123Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29779
    = surrogateDiagTailX0RatChunk001Sub001Block123Part002

theorem surrogateDiagonalTailChunk001Sub001Block123Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part002] using hcert

def TailChunk001Sub001Block123Part003SupportExplicit : Finset ℕ :=
  ([29782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block123Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29782
    = surrogateDiagTailX0RatChunk001Sub001Block123Part003

theorem surrogateDiagonalTailChunk001Sub001Block123Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part003] using hcert

def TailChunk001Sub001Block123Part004SupportExplicit : Finset ℕ :=
  ([29783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part004 : ℚ :=
  (248558439625 : ℚ) / 294918752295206387712

def SurrogateDiagonalTailChunk001Sub001Block123Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29783
    = surrogateDiagTailX0RatChunk001Sub001Block123Part004

theorem surrogateDiagonalTailChunk001Sub001Block123Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part004] using hcert

def TailChunk001Sub001Block123Part005SupportExplicit : Finset ℕ :=
  ([29785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part005 : ℚ :=
  (429393080975 : ℚ) / 54402806161770283008

def SurrogateDiagonalTailChunk001Sub001Block123Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29785
    = surrogateDiagTailX0RatChunk001Sub001Block123Part005

theorem surrogateDiagonalTailChunk001Sub001Block123Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part005] using hcert

def TailChunk001Sub001Block123Part006SupportExplicit : Finset ℕ :=
  ([29786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part006 : ℚ :=
  (148939009 : ℚ) / 160536695350886400

def SurrogateDiagonalTailChunk001Sub001Block123Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29786
    = surrogateDiagTailX0RatChunk001Sub001Block123Part006

theorem surrogateDiagonalTailChunk001Sub001Block123Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part006] using hcert

def TailChunk001Sub001Block123Part007SupportExplicit : Finset ℕ :=
  ([29787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part007 : ℚ :=
  (125025 : ℚ) / 77720763975630848

def SurrogateDiagonalTailChunk001Sub001Block123Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29787
    = surrogateDiagTailX0RatChunk001Sub001Block123Part007

theorem surrogateDiagonalTailChunk001Sub001Block123Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part007] using hcert

def TailChunk001Sub001Block123Part008SupportExplicit : Finset ℕ :=
  ([29789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block123Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29789
    = surrogateDiagTailX0RatChunk001Sub001Block123Part008

theorem surrogateDiagonalTailChunk001Sub001Block123Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part008] using hcert

def TailChunk001Sub001Block123Part009SupportExplicit : Finset ℕ :=
  ([29793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part009 : ℚ :=
  (1667 : ℚ) / 1037112139094400

def SurrogateDiagonalTailChunk001Sub001Block123Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29793
    = surrogateDiagTailX0RatChunk001Sub001Block123Part009

theorem surrogateDiagonalTailChunk001Sub001Block123Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part009] using hcert

def TailChunk001Sub001Block123Part010SupportExplicit : Finset ℕ :=
  ([29794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block123Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29794
    = surrogateDiagTailX0RatChunk001Sub001Block123Part010

theorem surrogateDiagonalTailChunk001Sub001Block123Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part010] using hcert

def TailChunk001Sub001Block123Part011SupportExplicit : Finset ℕ :=
  ([29795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part011 : ℚ :=
  (3832306101 : ℚ) / 1207334325248000000

def SurrogateDiagonalTailChunk001Sub001Block123Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29795
    = surrogateDiagTailX0RatChunk001Sub001Block123Part011

theorem surrogateDiagonalTailChunk001Sub001Block123Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part011] using hcert

def TailChunk001Sub001Block123Part012SupportExplicit : Finset ℕ :=
  ([29797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part012 : ℚ :=
  (137380845475 : ℚ) / 1857010566867478174848

def SurrogateDiagonalTailChunk001Sub001Block123Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29797
    = surrogateDiagTailX0RatChunk001Sub001Block123Part012

theorem surrogateDiagonalTailChunk001Sub001Block123Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part012] using hcert

def TailChunk001Sub001Block123Part013SupportExplicit : Finset ℕ :=
  ([29798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part013 : ℚ :=
  (113883113275 : ℚ) / 111636578130374903808

def SurrogateDiagonalTailChunk001Sub001Block123Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29798
    = surrogateDiagTailX0RatChunk001Sub001Block123Part013

theorem surrogateDiagonalTailChunk001Sub001Block123Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part013] using hcert

def TailChunk001Sub001Block123Part014SupportExplicit : Finset ℕ :=
  ([29801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part014 : ℚ :=
  (4029866575 : ℚ) / 10722121019138506752

def SurrogateDiagonalTailChunk001Sub001Block123Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29801
    = surrogateDiagTailX0RatChunk001Sub001Block123Part014

theorem surrogateDiagonalTailChunk001Sub001Block123Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part014] using hcert

def TailChunk001Sub001Block123Part015SupportExplicit : Finset ℕ :=
  ([29802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part015 : ℚ :=
  (770973656675 : ℚ) / 12165884995587745344

def SurrogateDiagonalTailChunk001Sub001Block123Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29802
    = surrogateDiagTailX0RatChunk001Sub001Block123Part015

theorem surrogateDiagonalTailChunk001Sub001Block123Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part015] using hcert

def TailChunk001Sub001Block123Part016SupportExplicit : Finset ℕ :=
  ([29803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block123Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29803
    = surrogateDiagTailX0RatChunk001Sub001Block123Part016

theorem surrogateDiagonalTailChunk001Sub001Block123Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part016] using hcert

def TailChunk001Sub001Block123Part017SupportExplicit : Finset ℕ :=
  ([29805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part017 : ℚ :=
  (185233695425 : ℚ) / 19916535581226602496

def SurrogateDiagonalTailChunk001Sub001Block123Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29805
    = surrogateDiagTailX0RatChunk001Sub001Block123Part017

theorem surrogateDiagonalTailChunk001Sub001Block123Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part017] using hcert

def TailChunk001Sub001Block123Part018SupportExplicit : Finset ℕ :=
  ([29806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part018 : ℚ :=
  (964407025 : ℚ) / 75344190258806784

def SurrogateDiagonalTailChunk001Sub001Block123Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29806
    = surrogateDiagTailX0RatChunk001Sub001Block123Part018

theorem surrogateDiagonalTailChunk001Sub001Block123Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part018] using hcert

def TailChunk001Sub001Block123Part019SupportExplicit : Finset ℕ :=
  ([29807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part019 : ℚ :=
  (607062547 : ℚ) / 4445834745567283200

def SurrogateDiagonalTailChunk001Sub001Block123Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29807
    = surrogateDiagTailX0RatChunk001Sub001Block123Part019

theorem surrogateDiagonalTailChunk001Sub001Block123Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part019] using hcert

def TailChunk001Sub001Block123Part020SupportExplicit : Finset ℕ :=
  ([29809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part020 : ℚ :=
  (73364456225 : ℚ) / 158989259578906017792

def SurrogateDiagonalTailChunk001Sub001Block123Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29809
    = surrogateDiagTailX0RatChunk001Sub001Block123Part020

theorem surrogateDiagonalTailChunk001Sub001Block123Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part020] using hcert

def TailChunk001Sub001Block123Part021SupportExplicit : Finset ℕ :=
  ([29810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part021 : ℚ :=
  (1068077009 : ℚ) / 30239134617600000

def SurrogateDiagonalTailChunk001Sub001Block123Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29810
    = surrogateDiagTailX0RatChunk001Sub001Block123Part021

theorem surrogateDiagonalTailChunk001Sub001Block123Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part021] using hcert

def TailChunk001Sub001Block123Part022SupportExplicit : Finset ℕ :=
  ([29811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part022 : ℚ :=
  (158935434725 : ℚ) / 155915351558021735424

def SurrogateDiagonalTailChunk001Sub001Block123Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29811
    = surrogateDiagTailX0RatChunk001Sub001Block123Part022

theorem surrogateDiagonalTailChunk001Sub001Block123Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part022] using hcert

def TailChunk001Sub001Block123Part023SupportExplicit : Finset ℕ :=
  ([29813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part023 : ℚ :=
  (1135035212725 : ℚ) / 1065257225947651886208

def SurrogateDiagonalTailChunk001Sub001Block123Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29813
    = surrogateDiagTailX0RatChunk001Sub001Block123Part023

theorem surrogateDiagonalTailChunk001Sub001Block123Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part023] using hcert

def TailChunk001Sub001Block123Part024SupportExplicit : Finset ℕ :=
  ([29814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block123Part024 : ℚ :=
  (385797265825 : ℚ) / 6092747762777137152

def SurrogateDiagonalTailChunk001Sub001Block123Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29814
    = surrogateDiagTailX0RatChunk001Sub001Block123Part024

theorem surrogateDiagonalTailChunk001Sub001Block123Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block123Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block123Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block123Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block123Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block123Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block123HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block123Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block123Part000
    + surrogateDiagTailX0RatChunk001Sub001Block123Part001
    + surrogateDiagTailX0RatChunk001Sub001Block123Part002
    + surrogateDiagTailX0RatChunk001Sub001Block123Part003
    + surrogateDiagTailX0RatChunk001Sub001Block123Part004
    + surrogateDiagTailX0RatChunk001Sub001Block123Part005
    + surrogateDiagTailX0RatChunk001Sub001Block123Part006
    + surrogateDiagTailX0RatChunk001Sub001Block123Part007
    + surrogateDiagTailX0RatChunk001Sub001Block123Part008
    + surrogateDiagTailX0RatChunk001Sub001Block123Part009

def surrogateDiagonalTailChunk001Sub001Block123MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block123Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block123Part010
    + surrogateDiagTailX0RatChunk001Sub001Block123Part011
    + surrogateDiagTailX0RatChunk001Sub001Block123Part012
    + surrogateDiagTailX0RatChunk001Sub001Block123Part013
    + surrogateDiagTailX0RatChunk001Sub001Block123Part014
    + surrogateDiagTailX0RatChunk001Sub001Block123Part015
    + surrogateDiagTailX0RatChunk001Sub001Block123Part016
    + surrogateDiagTailX0RatChunk001Sub001Block123Part017
    + surrogateDiagTailX0RatChunk001Sub001Block123Part018
    + surrogateDiagTailX0RatChunk001Sub001Block123Part019

def surrogateDiagonalTailChunk001Sub001Block123TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block123Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block123Part020
    + surrogateDiagTailX0RatChunk001Sub001Block123Part021
    + surrogateDiagTailX0RatChunk001Sub001Block123Part022
    + surrogateDiagTailX0RatChunk001Sub001Block123Part023
    + surrogateDiagTailX0RatChunk001Sub001Block123Part024

def surrogateDiagonalTailChunk001Sub001Block123Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block123HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block123MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block123TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block123 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block123Part000
    + surrogateDiagTailX0RatChunk001Sub001Block123Part001
    + surrogateDiagTailX0RatChunk001Sub001Block123Part002
    + surrogateDiagTailX0RatChunk001Sub001Block123Part003
    + surrogateDiagTailX0RatChunk001Sub001Block123Part004
    + surrogateDiagTailX0RatChunk001Sub001Block123Part005
    + surrogateDiagTailX0RatChunk001Sub001Block123Part006
    + surrogateDiagTailX0RatChunk001Sub001Block123Part007
    + surrogateDiagTailX0RatChunk001Sub001Block123Part008
    + surrogateDiagTailX0RatChunk001Sub001Block123Part009
    + surrogateDiagTailX0RatChunk001Sub001Block123Part010
    + surrogateDiagTailX0RatChunk001Sub001Block123Part011
    + surrogateDiagTailX0RatChunk001Sub001Block123Part012
    + surrogateDiagTailX0RatChunk001Sub001Block123Part013
    + surrogateDiagTailX0RatChunk001Sub001Block123Part014
    + surrogateDiagTailX0RatChunk001Sub001Block123Part015
    + surrogateDiagTailX0RatChunk001Sub001Block123Part016
    + surrogateDiagTailX0RatChunk001Sub001Block123Part017
    + surrogateDiagTailX0RatChunk001Sub001Block123Part018
    + surrogateDiagTailX0RatChunk001Sub001Block123Part019
    + surrogateDiagTailX0RatChunk001Sub001Block123Part020
    + surrogateDiagTailX0RatChunk001Sub001Block123Part021
    + surrogateDiagTailX0RatChunk001Sub001Block123Part022
    + surrogateDiagTailX0RatChunk001Sub001Block123Part023
    + surrogateDiagTailX0RatChunk001Sub001Block123Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block123_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block123Head + surrogateDiagTailX0RatChunk001Sub001Block123Mid + surrogateDiagTailX0RatChunk001Sub001Block123Tail =
      surrogateDiagTailX0RatChunk001Sub001Block123 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block123Head surrogateDiagTailX0RatChunk001Sub001Block123Mid surrogateDiagTailX0RatChunk001Sub001Block123Tail surrogateDiagTailX0RatChunk001Sub001Block123
  ring

def SurrogateDiagonalTailChunk001Sub001Block123HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block123HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block123Head

def SurrogateDiagonalTailChunk001Sub001Block123MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block123MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block123Mid

def SurrogateDiagonalTailChunk001Sub001Block123TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block123TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block123Tail

theorem surrogateDiagonalTailChunk001Sub001Block123_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block123HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block123MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block123TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block123Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block123 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block123HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block123MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block123TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block123Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block123_eq_head_add_mid_add_tail

/-- Block 124 covers tail-support indices [18100,18125) and q from 29815 to 29857. -/

def TailChunk001Sub001Block124Part000SupportExplicit : Finset ℕ :=
  ([29815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part000 : ℚ :=
  (255325668425 : ℚ) / 80933951634860408832

def SurrogateDiagonalTailChunk001Sub001Block124Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29815
    = surrogateDiagTailX0RatChunk001Sub001Block124Part000

theorem surrogateDiagonalTailChunk001Sub001Block124Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part000] using hcert

def TailChunk001Sub001Block124Part001SupportExplicit : Finset ℕ :=
  ([29818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part001 : ℚ :=
  (244611811525 : ℚ) / 96499089172246560768

def SurrogateDiagonalTailChunk001Sub001Block124Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29818
    = surrogateDiagTailX0RatChunk001Sub001Block124Part001

theorem surrogateDiagonalTailChunk001Sub001Block124Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part001] using hcert

def TailChunk001Sub001Block124Part002SupportExplicit : Finset ℕ :=
  ([29819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block124Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29819
    = surrogateDiagTailX0RatChunk001Sub001Block124Part002

theorem surrogateDiagonalTailChunk001Sub001Block124Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part002] using hcert

def TailChunk001Sub001Block124Part003SupportExplicit : Finset ℕ :=
  ([29821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part003 : ℚ :=
  (2302391149 : ℚ) / 3371661998185125000

def SurrogateDiagonalTailChunk001Sub001Block124Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29821
    = surrogateDiagTailX0RatChunk001Sub001Block124Part003

theorem surrogateDiagonalTailChunk001Sub001Block124Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part003] using hcert

def TailChunk001Sub001Block124Part004SupportExplicit : Finset ℕ :=
  ([29822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part004 : ℚ :=
  (485948333 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk001Sub001Block124Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29822
    = surrogateDiagTailX0RatChunk001Sub001Block124Part004

theorem surrogateDiagonalTailChunk001Sub001Block124Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part004] using hcert

def TailChunk001Sub001Block124Part005SupportExplicit : Finset ℕ :=
  ([29823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part005 : ℚ :=
  (5001 : ℚ) / 3123888439347200

def SurrogateDiagonalTailChunk001Sub001Block124Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29823
    = surrogateDiagTailX0RatChunk001Sub001Block124Part005

theorem surrogateDiagonalTailChunk001Sub001Block124Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part005] using hcert

def TailChunk001Sub001Block124Part006SupportExplicit : Finset ℕ :=
  ([29827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part006 : ℚ :=
  (45443998513 : ℚ) / 42690402367694899200

def SurrogateDiagonalTailChunk001Sub001Block124Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29827
    = surrogateDiagTailX0RatChunk001Sub001Block124Part006

theorem surrogateDiagonalTailChunk001Sub001Block124Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part006] using hcert

def TailChunk001Sub001Block124Part007SupportExplicit : Finset ℕ :=
  ([29829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part007 : ℚ :=
  (5494728643 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub001Block124Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29829
    = surrogateDiagTailX0RatChunk001Sub001Block124Part007

theorem surrogateDiagonalTailChunk001Sub001Block124Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part007] using hcert

def TailChunk001Sub001Block124Part008SupportExplicit : Finset ℕ :=
  ([29830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part008 : ℚ :=
  (1212935097925 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk001Sub001Block124Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29830
    = surrogateDiagTailX0RatChunk001Sub001Block124Part008

theorem surrogateDiagonalTailChunk001Sub001Block124Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part008] using hcert

def TailChunk001Sub001Block124Part009SupportExplicit : Finset ℕ :=
  ([29831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part009 : ℚ :=
  (71086201225 : ℚ) / 275414206193962057728

def SurrogateDiagonalTailChunk001Sub001Block124Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29831
    = surrogateDiagTailX0RatChunk001Sub001Block124Part009

theorem surrogateDiagonalTailChunk001Sub001Block124Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part009] using hcert

def TailChunk001Sub001Block124Part010SupportExplicit : Finset ℕ :=
  ([29833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block124Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29833
    = surrogateDiagTailX0RatChunk001Sub001Block124Part010

theorem surrogateDiagonalTailChunk001Sub001Block124Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part010] using hcert

def TailChunk001Sub001Block124Part011SupportExplicit : Finset ℕ :=
  ([29834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part011 : ℚ :=
  (11377477427 : ℚ) / 1334075073990465600

def SurrogateDiagonalTailChunk001Sub001Block124Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29834
    = surrogateDiagTailX0RatChunk001Sub001Block124Part011

theorem surrogateDiagonalTailChunk001Sub001Block124Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part011] using hcert

def TailChunk001Sub001Block124Part012SupportExplicit : Finset ℕ :=
  ([29837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block124Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29837
    = surrogateDiagTailX0RatChunk001Sub001Block124Part012

theorem surrogateDiagonalTailChunk001Sub001Block124Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part012] using hcert

def TailChunk001Sub001Block124Part013SupportExplicit : Finset ℕ :=
  ([29838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part013 : ℚ :=
  (48302314475 : ℚ) / 764049231258713664

def SurrogateDiagonalTailChunk001Sub001Block124Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29838
    = surrogateDiagTailX0RatChunk001Sub001Block124Part013

theorem surrogateDiagonalTailChunk001Sub001Block124Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part013] using hcert

def TailChunk001Sub001Block124Part014SupportExplicit : Finset ℕ :=
  ([29839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part014 : ℚ :=
  (174060563575 : ℚ) / 1823834789986230847488

def SurrogateDiagonalTailChunk001Sub001Block124Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29839
    = surrogateDiagTailX0RatChunk001Sub001Block124Part014

theorem surrogateDiagonalTailChunk001Sub001Block124Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part014] using hcert

def TailChunk001Sub001Block124Part015SupportExplicit : Finset ℕ :=
  ([29842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part015 : ℚ :=
  (2317033975 : ℚ) / 2065069421001300672

def SurrogateDiagonalTailChunk001Sub001Block124Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29842
    = surrogateDiagTailX0RatChunk001Sub001Block124Part015

theorem surrogateDiagonalTailChunk001Sub001Block124Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part015] using hcert

def TailChunk001Sub001Block124Part016SupportExplicit : Finset ℕ :=
  ([29843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part016 : ℚ :=
  (3074372293 : ℚ) / 4508835023615385600

def SurrogateDiagonalTailChunk001Sub001Block124Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29843
    = surrogateDiagTailX0RatChunk001Sub001Block124Part016

theorem surrogateDiagonalTailChunk001Sub001Block124Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part016] using hcert

def TailChunk001Sub001Block124Part017SupportExplicit : Finset ℕ :=
  ([29845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part017 : ℚ :=
  (128507898025 : ℚ) / 40133573054671896576

def SurrogateDiagonalTailChunk001Sub001Block124Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29845
    = surrogateDiagTailX0RatChunk001Sub001Block124Part017

theorem surrogateDiagonalTailChunk001Sub001Block124Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part017] using hcert

def TailChunk001Sub001Block124Part018SupportExplicit : Finset ℕ :=
  ([29846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block124Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29846
    = surrogateDiagTailX0RatChunk001Sub001Block124Part018

theorem surrogateDiagonalTailChunk001Sub001Block124Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part018] using hcert

def TailChunk001Sub001Block124Part019SupportExplicit : Finset ℕ :=
  ([29847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part019 : ℚ :=
  (41675 : ℚ) / 26116311421310976

def SurrogateDiagonalTailChunk001Sub001Block124Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29847
    = surrogateDiagTailX0RatChunk001Sub001Block124Part019

theorem surrogateDiagonalTailChunk001Sub001Block124Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part019] using hcert

def TailChunk001Sub001Block124Part020SupportExplicit : Finset ℕ :=
  ([29849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part020 : ℚ :=
  (18704272483 : ℚ) / 63793360469045635200

def SurrogateDiagonalTailChunk001Sub001Block124Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29849
    = surrogateDiagTailX0RatChunk001Sub001Block124Part020

theorem surrogateDiagonalTailChunk001Sub001Block124Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part020] using hcert

def TailChunk001Sub001Block124Part021SupportExplicit : Finset ℕ :=
  ([29851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block124Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29851
    = surrogateDiagTailX0RatChunk001Sub001Block124Part021

theorem surrogateDiagonalTailChunk001Sub001Block124Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part021] using hcert

def TailChunk001Sub001Block124Part022SupportExplicit : Finset ℕ :=
  ([29854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part022 : ℚ :=
  (4397310747 : ℚ) / 441914546398899200

def SurrogateDiagonalTailChunk001Sub001Block124Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29854
    = surrogateDiagTailX0RatChunk001Sub001Block124Part022

theorem surrogateDiagonalTailChunk001Sub001Block124Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part022] using hcert

def TailChunk001Sub001Block124Part023SupportExplicit : Finset ℕ :=
  ([29855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part023 : ℚ :=
  (53090570575 : ℚ) / 9107285838441578496

def SurrogateDiagonalTailChunk001Sub001Block124Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29855
    = surrogateDiagTailX0RatChunk001Sub001Block124Part023

theorem surrogateDiagonalTailChunk001Sub001Block124Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part023] using hcert

def TailChunk001Sub001Block124Part024SupportExplicit : Finset ℕ :=
  ([29857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block124Part024 : ℚ :=
  (18365052125 : ℚ) / 232759550582467854336

def SurrogateDiagonalTailChunk001Sub001Block124Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29857
    = surrogateDiagTailX0RatChunk001Sub001Block124Part024

theorem surrogateDiagonalTailChunk001Sub001Block124Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block124Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block124Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block124Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block124Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block124Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block124HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block124Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block124Part000
    + surrogateDiagTailX0RatChunk001Sub001Block124Part001
    + surrogateDiagTailX0RatChunk001Sub001Block124Part002
    + surrogateDiagTailX0RatChunk001Sub001Block124Part003
    + surrogateDiagTailX0RatChunk001Sub001Block124Part004
    + surrogateDiagTailX0RatChunk001Sub001Block124Part005
    + surrogateDiagTailX0RatChunk001Sub001Block124Part006
    + surrogateDiagTailX0RatChunk001Sub001Block124Part007
    + surrogateDiagTailX0RatChunk001Sub001Block124Part008
    + surrogateDiagTailX0RatChunk001Sub001Block124Part009

def surrogateDiagonalTailChunk001Sub001Block124MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block124Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block124Part010
    + surrogateDiagTailX0RatChunk001Sub001Block124Part011
    + surrogateDiagTailX0RatChunk001Sub001Block124Part012
    + surrogateDiagTailX0RatChunk001Sub001Block124Part013
    + surrogateDiagTailX0RatChunk001Sub001Block124Part014
    + surrogateDiagTailX0RatChunk001Sub001Block124Part015
    + surrogateDiagTailX0RatChunk001Sub001Block124Part016
    + surrogateDiagTailX0RatChunk001Sub001Block124Part017
    + surrogateDiagTailX0RatChunk001Sub001Block124Part018
    + surrogateDiagTailX0RatChunk001Sub001Block124Part019

def surrogateDiagonalTailChunk001Sub001Block124TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block124Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block124Part020
    + surrogateDiagTailX0RatChunk001Sub001Block124Part021
    + surrogateDiagTailX0RatChunk001Sub001Block124Part022
    + surrogateDiagTailX0RatChunk001Sub001Block124Part023
    + surrogateDiagTailX0RatChunk001Sub001Block124Part024

def surrogateDiagonalTailChunk001Sub001Block124Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block124HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block124MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block124TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block124 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block124Part000
    + surrogateDiagTailX0RatChunk001Sub001Block124Part001
    + surrogateDiagTailX0RatChunk001Sub001Block124Part002
    + surrogateDiagTailX0RatChunk001Sub001Block124Part003
    + surrogateDiagTailX0RatChunk001Sub001Block124Part004
    + surrogateDiagTailX0RatChunk001Sub001Block124Part005
    + surrogateDiagTailX0RatChunk001Sub001Block124Part006
    + surrogateDiagTailX0RatChunk001Sub001Block124Part007
    + surrogateDiagTailX0RatChunk001Sub001Block124Part008
    + surrogateDiagTailX0RatChunk001Sub001Block124Part009
    + surrogateDiagTailX0RatChunk001Sub001Block124Part010
    + surrogateDiagTailX0RatChunk001Sub001Block124Part011
    + surrogateDiagTailX0RatChunk001Sub001Block124Part012
    + surrogateDiagTailX0RatChunk001Sub001Block124Part013
    + surrogateDiagTailX0RatChunk001Sub001Block124Part014
    + surrogateDiagTailX0RatChunk001Sub001Block124Part015
    + surrogateDiagTailX0RatChunk001Sub001Block124Part016
    + surrogateDiagTailX0RatChunk001Sub001Block124Part017
    + surrogateDiagTailX0RatChunk001Sub001Block124Part018
    + surrogateDiagTailX0RatChunk001Sub001Block124Part019
    + surrogateDiagTailX0RatChunk001Sub001Block124Part020
    + surrogateDiagTailX0RatChunk001Sub001Block124Part021
    + surrogateDiagTailX0RatChunk001Sub001Block124Part022
    + surrogateDiagTailX0RatChunk001Sub001Block124Part023
    + surrogateDiagTailX0RatChunk001Sub001Block124Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block124_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block124Head + surrogateDiagTailX0RatChunk001Sub001Block124Mid + surrogateDiagTailX0RatChunk001Sub001Block124Tail =
      surrogateDiagTailX0RatChunk001Sub001Block124 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block124Head surrogateDiagTailX0RatChunk001Sub001Block124Mid surrogateDiagTailX0RatChunk001Sub001Block124Tail surrogateDiagTailX0RatChunk001Sub001Block124
  ring

def SurrogateDiagonalTailChunk001Sub001Block124HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block124HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block124Head

def SurrogateDiagonalTailChunk001Sub001Block124MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block124MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block124Mid

def SurrogateDiagonalTailChunk001Sub001Block124TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block124TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block124Tail

theorem surrogateDiagonalTailChunk001Sub001Block124_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block124HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block124MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block124TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block124Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block124 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block124HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block124MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block124TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block124Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block124_eq_head_add_mid_add_tail

/-- Block 125 covers tail-support indices [18125,18150) and q from 29858 to 29899. -/

def TailChunk001Sub001Block125Part000SupportExplicit : Finset ℕ :=
  ([29858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29858
    = surrogateDiagTailX0RatChunk001Sub001Block125Part000

theorem surrogateDiagonalTailChunk001Sub001Block125Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part000] using hcert

def TailChunk001Sub001Block125Part001SupportExplicit : Finset ℕ :=
  ([29859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part001 : ℚ :=
  (188605746775 : ℚ) / 346653844260719689728

def SurrogateDiagonalTailChunk001Sub001Block125Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29859
    = surrogateDiagTailX0RatChunk001Sub001Block125Part001

theorem surrogateDiagonalTailChunk001Sub001Block125Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part001] using hcert

def TailChunk001Sub001Block125Part002SupportExplicit : Finset ℕ :=
  ([29861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part002 : ℚ :=
  (662573646025 : ℚ) / 1440918369484166135808

def SurrogateDiagonalTailChunk001Sub001Block125Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29861
    = surrogateDiagTailX0RatChunk001Sub001Block125Part002

theorem surrogateDiagonalTailChunk001Sub001Block125Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part002] using hcert

def TailChunk001Sub001Block125Part003SupportExplicit : Finset ℕ :=
  ([29863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29863
    = surrogateDiagTailX0RatChunk001Sub001Block125Part003

theorem surrogateDiagonalTailChunk001Sub001Block125Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part003] using hcert

def TailChunk001Sub001Block125Part004SupportExplicit : Finset ℕ :=
  ([29865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part004 : ℚ :=
  (60379444057 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk001Sub001Block125Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29865
    = surrogateDiagTailX0RatChunk001Sub001Block125Part004

theorem surrogateDiagonalTailChunk001Sub001Block125Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part004] using hcert

def TailChunk001Sub001Block125Part005SupportExplicit : Finset ℕ :=
  ([29866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part005 : ℚ :=
  (25435287875 : ℚ) / 38793258430411309056

def SurrogateDiagonalTailChunk001Sub001Block125Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29866
    = surrogateDiagTailX0RatChunk001Sub001Block125Part005

theorem surrogateDiagonalTailChunk001Sub001Block125Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part005] using hcert

def TailChunk001Sub001Block125Part006SupportExplicit : Finset ℕ :=
  ([29867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29867
    = surrogateDiagTailX0RatChunk001Sub001Block125Part006

theorem surrogateDiagonalTailChunk001Sub001Block125Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part006] using hcert

def TailChunk001Sub001Block125Part007SupportExplicit : Finset ℕ :=
  ([29869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part007 : ℚ :=
  (30209013737 : ℚ) / 16592117760000000000

def SurrogateDiagonalTailChunk001Sub001Block125Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29869
    = surrogateDiagTailX0RatChunk001Sub001Block125Part007

theorem surrogateDiagonalTailChunk001Sub001Block125Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part007] using hcert

def TailChunk001Sub001Block125Part008SupportExplicit : Finset ℕ :=
  ([29870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part008 : ℚ :=
  (168760794625 : ℚ) / 6084173590137667584

def SurrogateDiagonalTailChunk001Sub001Block125Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29870
    = surrogateDiagTailX0RatChunk001Sub001Block125Part008

theorem surrogateDiagonalTailChunk001Sub001Block125Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part008] using hcert

def TailChunk001Sub001Block125Part009SupportExplicit : Finset ℕ :=
  ([29873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29873
    = surrogateDiagTailX0RatChunk001Sub001Block125Part009

theorem surrogateDiagonalTailChunk001Sub001Block125Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part009] using hcert

def TailChunk001Sub001Block125Part010SupportExplicit : Finset ℕ :=
  ([29874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part010 : ℚ :=
  (192466868975 : ℚ) / 2208184160818139136

def SurrogateDiagonalTailChunk001Sub001Block125Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29874
    = surrogateDiagTailX0RatChunk001Sub001Block125Part010

theorem surrogateDiagonalTailChunk001Sub001Block125Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part010] using hcert

def TailChunk001Sub001Block125Part011SupportExplicit : Finset ℕ :=
  ([29877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part011 : ℚ :=
  (146844766025 : ℚ) / 163208418485310849024

def SurrogateDiagonalTailChunk001Sub001Block125Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29877
    = surrogateDiagTailX0RatChunk001Sub001Block125Part011

theorem surrogateDiagonalTailChunk001Sub001Block125Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part011] using hcert

def TailChunk001Sub001Block125Part012SupportExplicit : Finset ℕ :=
  ([29878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29878
    = surrogateDiagTailX0RatChunk001Sub001Block125Part012

theorem surrogateDiagonalTailChunk001Sub001Block125Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part012] using hcert

def TailChunk001Sub001Block125Part013SupportExplicit : Finset ℕ :=
  ([29879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29879
    = surrogateDiagTailX0RatChunk001Sub001Block125Part013

theorem surrogateDiagonalTailChunk001Sub001Block125Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part013] using hcert

def TailChunk001Sub001Block125Part014SupportExplicit : Finset ℕ :=
  ([29881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29881
    = surrogateDiagTailX0RatChunk001Sub001Block125Part014

theorem surrogateDiagonalTailChunk001Sub001Block125Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part014] using hcert

def TailChunk001Sub001Block125Part015SupportExplicit : Finset ℕ :=
  ([29882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part015 : ℚ :=
  (22051159225 : ℚ) / 28810746256213592352

def SurrogateDiagonalTailChunk001Sub001Block125Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29882
    = surrogateDiagTailX0RatChunk001Sub001Block125Part015

theorem surrogateDiagonalTailChunk001Sub001Block125Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part015] using hcert

def TailChunk001Sub001Block125Part016SupportExplicit : Finset ℕ :=
  ([29883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part016 : ℚ :=
  (1058375 : ℚ) / 294395306620032

def SurrogateDiagonalTailChunk001Sub001Block125Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29883
    = surrogateDiagTailX0RatChunk001Sub001Block125Part016

theorem surrogateDiagonalTailChunk001Sub001Block125Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part016] using hcert

def TailChunk001Sub001Block125Part017SupportExplicit : Finset ℕ :=
  ([29885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part017 : ℚ :=
  (772775095375 : ℚ) / 240801438328031379456

def SurrogateDiagonalTailChunk001Sub001Block125Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29885
    = surrogateDiagTailX0RatChunk001Sub001Block125Part017

theorem surrogateDiagonalTailChunk001Sub001Block125Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part017] using hcert

def TailChunk001Sub001Block125Part018SupportExplicit : Finset ℕ :=
  ([29886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part018 : ℚ :=
  (16201579575 : ℚ) / 198557796650713088

def SurrogateDiagonalTailChunk001Sub001Block125Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29886
    = surrogateDiagTailX0RatChunk001Sub001Block125Part018

theorem surrogateDiagonalTailChunk001Sub001Block125Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part018] using hcert

def TailChunk001Sub001Block125Part019SupportExplicit : Finset ℕ :=
  ([29891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part019 : ℚ :=
  (6150424639 : ℚ) / 74726763324192000000

def SurrogateDiagonalTailChunk001Sub001Block125Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29891
    = surrogateDiagTailX0RatChunk001Sub001Block125Part019

theorem surrogateDiagonalTailChunk001Sub001Block125Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part019] using hcert

def TailChunk001Sub001Block125Part020SupportExplicit : Finset ℕ :=
  ([29893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part020 : ℚ :=
  (4392828075 : ℚ) / 79419651784535692592

def SurrogateDiagonalTailChunk001Sub001Block125Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29893
    = surrogateDiagTailX0RatChunk001Sub001Block125Part020

theorem surrogateDiagonalTailChunk001Sub001Block125Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part020] using hcert

def TailChunk001Sub001Block125Part021SupportExplicit : Finset ℕ :=
  ([29894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block125Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29894
    = surrogateDiagTailX0RatChunk001Sub001Block125Part021

theorem surrogateDiagonalTailChunk001Sub001Block125Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part021] using hcert

def TailChunk001Sub001Block125Part022SupportExplicit : Finset ℕ :=
  ([29895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part022 : ℚ :=
  (372705463375 : ℚ) / 40316623397062705152

def SurrogateDiagonalTailChunk001Sub001Block125Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29895
    = surrogateDiagTailX0RatChunk001Sub001Block125Part022

theorem surrogateDiagonalTailChunk001Sub001Block125Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part022] using hcert

def TailChunk001Sub001Block125Part023SupportExplicit : Finset ℕ :=
  ([29897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part023 : ℚ :=
  (45657248533 : ℚ) / 43092664865947267200

def SurrogateDiagonalTailChunk001Sub001Block125Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29897
    = surrogateDiagTailX0RatChunk001Sub001Block125Part023

theorem surrogateDiagonalTailChunk001Sub001Block125Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part023] using hcert

def TailChunk001Sub001Block125Part024SupportExplicit : Finset ℕ :=
  ([29899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block125Part024 : ℚ :=
  (1133327667 : ℚ) / 5766159193899865600

def SurrogateDiagonalTailChunk001Sub001Block125Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29899
    = surrogateDiagTailX0RatChunk001Sub001Block125Part024

theorem surrogateDiagonalTailChunk001Sub001Block125Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block125Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block125Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block125Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block125Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block125Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block125HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block125Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block125Part000
    + surrogateDiagTailX0RatChunk001Sub001Block125Part001
    + surrogateDiagTailX0RatChunk001Sub001Block125Part002
    + surrogateDiagTailX0RatChunk001Sub001Block125Part003
    + surrogateDiagTailX0RatChunk001Sub001Block125Part004
    + surrogateDiagTailX0RatChunk001Sub001Block125Part005
    + surrogateDiagTailX0RatChunk001Sub001Block125Part006
    + surrogateDiagTailX0RatChunk001Sub001Block125Part007
    + surrogateDiagTailX0RatChunk001Sub001Block125Part008
    + surrogateDiagTailX0RatChunk001Sub001Block125Part009

def surrogateDiagonalTailChunk001Sub001Block125MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block125Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block125Part010
    + surrogateDiagTailX0RatChunk001Sub001Block125Part011
    + surrogateDiagTailX0RatChunk001Sub001Block125Part012
    + surrogateDiagTailX0RatChunk001Sub001Block125Part013
    + surrogateDiagTailX0RatChunk001Sub001Block125Part014
    + surrogateDiagTailX0RatChunk001Sub001Block125Part015
    + surrogateDiagTailX0RatChunk001Sub001Block125Part016
    + surrogateDiagTailX0RatChunk001Sub001Block125Part017
    + surrogateDiagTailX0RatChunk001Sub001Block125Part018
    + surrogateDiagTailX0RatChunk001Sub001Block125Part019

def surrogateDiagonalTailChunk001Sub001Block125TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block125Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block125Part020
    + surrogateDiagTailX0RatChunk001Sub001Block125Part021
    + surrogateDiagTailX0RatChunk001Sub001Block125Part022
    + surrogateDiagTailX0RatChunk001Sub001Block125Part023
    + surrogateDiagTailX0RatChunk001Sub001Block125Part024

def surrogateDiagonalTailChunk001Sub001Block125Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block125HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block125MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block125TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block125 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block125Part000
    + surrogateDiagTailX0RatChunk001Sub001Block125Part001
    + surrogateDiagTailX0RatChunk001Sub001Block125Part002
    + surrogateDiagTailX0RatChunk001Sub001Block125Part003
    + surrogateDiagTailX0RatChunk001Sub001Block125Part004
    + surrogateDiagTailX0RatChunk001Sub001Block125Part005
    + surrogateDiagTailX0RatChunk001Sub001Block125Part006
    + surrogateDiagTailX0RatChunk001Sub001Block125Part007
    + surrogateDiagTailX0RatChunk001Sub001Block125Part008
    + surrogateDiagTailX0RatChunk001Sub001Block125Part009
    + surrogateDiagTailX0RatChunk001Sub001Block125Part010
    + surrogateDiagTailX0RatChunk001Sub001Block125Part011
    + surrogateDiagTailX0RatChunk001Sub001Block125Part012
    + surrogateDiagTailX0RatChunk001Sub001Block125Part013
    + surrogateDiagTailX0RatChunk001Sub001Block125Part014
    + surrogateDiagTailX0RatChunk001Sub001Block125Part015
    + surrogateDiagTailX0RatChunk001Sub001Block125Part016
    + surrogateDiagTailX0RatChunk001Sub001Block125Part017
    + surrogateDiagTailX0RatChunk001Sub001Block125Part018
    + surrogateDiagTailX0RatChunk001Sub001Block125Part019
    + surrogateDiagTailX0RatChunk001Sub001Block125Part020
    + surrogateDiagTailX0RatChunk001Sub001Block125Part021
    + surrogateDiagTailX0RatChunk001Sub001Block125Part022
    + surrogateDiagTailX0RatChunk001Sub001Block125Part023
    + surrogateDiagTailX0RatChunk001Sub001Block125Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block125_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block125Head + surrogateDiagTailX0RatChunk001Sub001Block125Mid + surrogateDiagTailX0RatChunk001Sub001Block125Tail =
      surrogateDiagTailX0RatChunk001Sub001Block125 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block125Head surrogateDiagTailX0RatChunk001Sub001Block125Mid surrogateDiagTailX0RatChunk001Sub001Block125Tail surrogateDiagTailX0RatChunk001Sub001Block125
  ring

def SurrogateDiagonalTailChunk001Sub001Block125HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block125HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block125Head

def SurrogateDiagonalTailChunk001Sub001Block125MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block125MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block125Mid

def SurrogateDiagonalTailChunk001Sub001Block125TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block125TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block125Tail

theorem surrogateDiagonalTailChunk001Sub001Block125_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block125HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block125MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block125TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block125Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block125 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block125HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block125MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block125TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block125Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block125_eq_head_add_mid_add_tail

/-- Block 126 covers tail-support indices [18150,18175) and q from 29901 to 29941. -/

def TailChunk001Sub001Block126Part000SupportExplicit : Finset ℕ :=
  ([29901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part000 : ℚ :=
  (41675 : ℚ) / 26305845411136896

def SurrogateDiagonalTailChunk001Sub001Block126Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29901
    = surrogateDiagTailX0RatChunk001Sub001Block126Part000

theorem surrogateDiagonalTailChunk001Sub001Block126Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part000] using hcert

def TailChunk001Sub001Block126Part001SupportExplicit : Finset ℕ :=
  ([29902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block126Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29902
    = surrogateDiagTailX0RatChunk001Sub001Block126Part001

theorem surrogateDiagonalTailChunk001Sub001Block126Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part001] using hcert

def TailChunk001Sub001Block126Part002SupportExplicit : Finset ℕ :=
  ([29903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part002 : ℚ :=
  (16229109925 : ℚ) / 43479022502177538048

def SurrogateDiagonalTailChunk001Sub001Block126Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29903
    = surrogateDiagTailX0RatChunk001Sub001Block126Part002

theorem surrogateDiagonalTailChunk001Sub001Block126Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part002] using hcert

def TailChunk001Sub001Block126Part003SupportExplicit : Finset ℕ :=
  ([29905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part003 : ℚ :=
  (5963401173 : ℚ) / 2182932427778785280

def SurrogateDiagonalTailChunk001Sub001Block126Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29905
    = surrogateDiagTailX0RatChunk001Sub001Block126Part003

theorem surrogateDiagonalTailChunk001Sub001Block126Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part003] using hcert

def TailChunk001Sub001Block126Part004SupportExplicit : Finset ℕ :=
  ([29906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part004 : ℚ :=
  (118532107475 : ℚ) / 50093003002452554304

def SurrogateDiagonalTailChunk001Sub001Block126Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29906
    = surrogateDiagTailX0RatChunk001Sub001Block126Part004

theorem surrogateDiagonalTailChunk001Sub001Block126Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part004] using hcert

def TailChunk001Sub001Block126Part005SupportExplicit : Finset ℕ :=
  ([29909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part005 : ℚ :=
  (771986143 : ℚ) / 1137217207348877400

def SurrogateDiagonalTailChunk001Sub001Block126Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29909
    = surrogateDiagTailX0RatChunk001Sub001Block126Part005

theorem surrogateDiagonalTailChunk001Sub001Block126Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part005] using hcert

def TailChunk001Sub001Block126Part006SupportExplicit : Finset ℕ :=
  ([29910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part006 : ℚ :=
  (1428696312325 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk001Sub001Block126Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29910
    = surrogateDiagTailX0RatChunk001Sub001Block126Part006

theorem surrogateDiagonalTailChunk001Sub001Block126Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part006] using hcert

def TailChunk001Sub001Block126Part007SupportExplicit : Finset ℕ :=
  ([29911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part007 : ℚ :=
  (1142498963425 : ℚ) / 1079336431962397605888

def SurrogateDiagonalTailChunk001Sub001Block126Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29911
    = surrogateDiagTailX0RatChunk001Sub001Block126Part007

theorem surrogateDiagonalTailChunk001Sub001Block126Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part007] using hcert

def TailChunk001Sub001Block126Part008SupportExplicit : Finset ℕ :=
  ([29914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block126Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29914
    = surrogateDiagTailX0RatChunk001Sub001Block126Part008

theorem surrogateDiagonalTailChunk001Sub001Block126Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part008] using hcert

def TailChunk001Sub001Block126Part009SupportExplicit : Finset ℕ :=
  ([29915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part009 : ℚ :=
  (1040924137 : ℚ) / 313165736501575680

def SurrogateDiagonalTailChunk001Sub001Block126Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29915
    = surrogateDiagTailX0RatChunk001Sub001Block126Part009

theorem surrogateDiagonalTailChunk001Sub001Block126Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part009] using hcert

def TailChunk001Sub001Block126Part010SupportExplicit : Finset ℕ :=
  ([29917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block126Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29917
    = surrogateDiagTailX0RatChunk001Sub001Block126Part010

theorem surrogateDiagonalTailChunk001Sub001Block126Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part010] using hcert

def TailChunk001Sub001Block126Part011SupportExplicit : Finset ℕ :=
  ([29918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part011 : ℚ :=
  (15870378475 : ℚ) / 1249231981437960192

def SurrogateDiagonalTailChunk001Sub001Block126Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29918
    = surrogateDiagTailX0RatChunk001Sub001Block126Part011

theorem surrogateDiagonalTailChunk001Sub001Block126Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part011] using hcert

def TailChunk001Sub001Block126Part012SupportExplicit : Finset ℕ :=
  ([29919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part012 : ℚ :=
  (41675 : ℚ) / 26369252060092416

def SurrogateDiagonalTailChunk001Sub001Block126Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29919
    = surrogateDiagTailX0RatChunk001Sub001Block126Part012

theorem surrogateDiagonalTailChunk001Sub001Block126Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part012] using hcert

def TailChunk001Sub001Block126Part013SupportExplicit : Finset ℕ :=
  ([29921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block126Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29921
    = surrogateDiagTailX0RatChunk001Sub001Block126Part013

theorem surrogateDiagonalTailChunk001Sub001Block126Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part013] using hcert

def TailChunk001Sub001Block126Part014SupportExplicit : Finset ℕ :=
  ([29922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part014 : ℚ :=
  (777193656425 : ℚ) / 12363059020548953664

def SurrogateDiagonalTailChunk001Sub001Block126Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29922
    = surrogateDiagTailX0RatChunk001Sub001Block126Part014

theorem surrogateDiagonalTailChunk001Sub001Block126Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part014] using hcert

def TailChunk001Sub001Block126Part015SupportExplicit : Finset ℕ :=
  ([29923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part015 : ℚ :=
  (8582233043 : ℚ) / 33459618665616000000

def SurrogateDiagonalTailChunk001Sub001Block126Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29923
    = surrogateDiagTailX0RatChunk001Sub001Block126Part015

theorem surrogateDiagonalTailChunk001Sub001Block126Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part015] using hcert

def TailChunk001Sub001Block126Part016SupportExplicit : Finset ℕ :=
  ([29926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part016 : ℚ :=
  (2227864699 : ℚ) / 604577451312000000

def SurrogateDiagonalTailChunk001Sub001Block126Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29926
    = surrogateDiagTailX0RatChunk001Sub001Block126Part016

theorem surrogateDiagonalTailChunk001Sub001Block126Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part016] using hcert

def TailChunk001Sub001Block126Part017SupportExplicit : Finset ℕ :=
  ([29927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block126Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29927
    = surrogateDiagTailX0RatChunk001Sub001Block126Part017

theorem surrogateDiagonalTailChunk001Sub001Block126Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part017] using hcert

def TailChunk001Sub001Block126Part018SupportExplicit : Finset ℕ :=
  ([29930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part018 : ℚ :=
  (6574665427 : ℚ) / 440389316955340800

def SurrogateDiagonalTailChunk001Sub001Block126Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29930
    = surrogateDiagTailX0RatChunk001Sub001Block126Part018

theorem surrogateDiagonalTailChunk001Sub001Block126Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part018] using hcert

def TailChunk001Sub001Block126Part019SupportExplicit : Finset ℕ :=
  ([29931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part019 : ℚ :=
  (3804597221 : ℚ) / 1797083981983411200

def SurrogateDiagonalTailChunk001Sub001Block126Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29931
    = surrogateDiagTailX0RatChunk001Sub001Block126Part019

theorem surrogateDiagonalTailChunk001Sub001Block126Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part019] using hcert

def TailChunk001Sub001Block126Part020SupportExplicit : Finset ℕ :=
  ([29933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part020 : ℚ :=
  (1579136875 : ℚ) / 11050127536286859264

def SurrogateDiagonalTailChunk001Sub001Block126Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29933
    = surrogateDiagTailX0RatChunk001Sub001Block126Part020

theorem surrogateDiagonalTailChunk001Sub001Block126Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part020] using hcert

def TailChunk001Sub001Block126Part021SupportExplicit : Finset ℕ :=
  ([29935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part021 : ℚ :=
  (746920896375 : ℚ) / 273963319346443196416

def SurrogateDiagonalTailChunk001Sub001Block126Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29935
    = surrogateDiagTailX0RatChunk001Sub001Block126Part021

theorem surrogateDiagonalTailChunk001Sub001Block126Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part021] using hcert

def TailChunk001Sub001Block126Part022SupportExplicit : Finset ℕ :=
  ([29937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part022 : ℚ :=
  (39631575 : ℚ) / 30912233554837504

def SurrogateDiagonalTailChunk001Sub001Block126Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29937
    = surrogateDiagTailX0RatChunk001Sub001Block126Part022

theorem surrogateDiagonalTailChunk001Sub001Block126Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part022] using hcert

def TailChunk001Sub001Block126Part023SupportExplicit : Finset ℕ :=
  ([29938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block126Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29938
    = surrogateDiagTailX0RatChunk001Sub001Block126Part023

theorem surrogateDiagonalTailChunk001Sub001Block126Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part023] using hcert

def TailChunk001Sub001Block126Part024SupportExplicit : Finset ℕ :=
  ([29941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block126Part024 : ℚ :=
  (70042195625 : ℚ) / 944805631742602104384

def SurrogateDiagonalTailChunk001Sub001Block126Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29941
    = surrogateDiagTailX0RatChunk001Sub001Block126Part024

theorem surrogateDiagonalTailChunk001Sub001Block126Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block126Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block126Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block126Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block126Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block126Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block126HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block126Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block126Part000
    + surrogateDiagTailX0RatChunk001Sub001Block126Part001
    + surrogateDiagTailX0RatChunk001Sub001Block126Part002
    + surrogateDiagTailX0RatChunk001Sub001Block126Part003
    + surrogateDiagTailX0RatChunk001Sub001Block126Part004
    + surrogateDiagTailX0RatChunk001Sub001Block126Part005
    + surrogateDiagTailX0RatChunk001Sub001Block126Part006
    + surrogateDiagTailX0RatChunk001Sub001Block126Part007
    + surrogateDiagTailX0RatChunk001Sub001Block126Part008
    + surrogateDiagTailX0RatChunk001Sub001Block126Part009

def surrogateDiagonalTailChunk001Sub001Block126MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block126Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block126Part010
    + surrogateDiagTailX0RatChunk001Sub001Block126Part011
    + surrogateDiagTailX0RatChunk001Sub001Block126Part012
    + surrogateDiagTailX0RatChunk001Sub001Block126Part013
    + surrogateDiagTailX0RatChunk001Sub001Block126Part014
    + surrogateDiagTailX0RatChunk001Sub001Block126Part015
    + surrogateDiagTailX0RatChunk001Sub001Block126Part016
    + surrogateDiagTailX0RatChunk001Sub001Block126Part017
    + surrogateDiagTailX0RatChunk001Sub001Block126Part018
    + surrogateDiagTailX0RatChunk001Sub001Block126Part019

def surrogateDiagonalTailChunk001Sub001Block126TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block126Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block126Part020
    + surrogateDiagTailX0RatChunk001Sub001Block126Part021
    + surrogateDiagTailX0RatChunk001Sub001Block126Part022
    + surrogateDiagTailX0RatChunk001Sub001Block126Part023
    + surrogateDiagTailX0RatChunk001Sub001Block126Part024

def surrogateDiagonalTailChunk001Sub001Block126Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block126HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block126MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block126TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block126 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block126Part000
    + surrogateDiagTailX0RatChunk001Sub001Block126Part001
    + surrogateDiagTailX0RatChunk001Sub001Block126Part002
    + surrogateDiagTailX0RatChunk001Sub001Block126Part003
    + surrogateDiagTailX0RatChunk001Sub001Block126Part004
    + surrogateDiagTailX0RatChunk001Sub001Block126Part005
    + surrogateDiagTailX0RatChunk001Sub001Block126Part006
    + surrogateDiagTailX0RatChunk001Sub001Block126Part007
    + surrogateDiagTailX0RatChunk001Sub001Block126Part008
    + surrogateDiagTailX0RatChunk001Sub001Block126Part009
    + surrogateDiagTailX0RatChunk001Sub001Block126Part010
    + surrogateDiagTailX0RatChunk001Sub001Block126Part011
    + surrogateDiagTailX0RatChunk001Sub001Block126Part012
    + surrogateDiagTailX0RatChunk001Sub001Block126Part013
    + surrogateDiagTailX0RatChunk001Sub001Block126Part014
    + surrogateDiagTailX0RatChunk001Sub001Block126Part015
    + surrogateDiagTailX0RatChunk001Sub001Block126Part016
    + surrogateDiagTailX0RatChunk001Sub001Block126Part017
    + surrogateDiagTailX0RatChunk001Sub001Block126Part018
    + surrogateDiagTailX0RatChunk001Sub001Block126Part019
    + surrogateDiagTailX0RatChunk001Sub001Block126Part020
    + surrogateDiagTailX0RatChunk001Sub001Block126Part021
    + surrogateDiagTailX0RatChunk001Sub001Block126Part022
    + surrogateDiagTailX0RatChunk001Sub001Block126Part023
    + surrogateDiagTailX0RatChunk001Sub001Block126Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block126_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block126Head + surrogateDiagTailX0RatChunk001Sub001Block126Mid + surrogateDiagTailX0RatChunk001Sub001Block126Tail =
      surrogateDiagTailX0RatChunk001Sub001Block126 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block126Head surrogateDiagTailX0RatChunk001Sub001Block126Mid surrogateDiagTailX0RatChunk001Sub001Block126Tail surrogateDiagTailX0RatChunk001Sub001Block126
  ring

def SurrogateDiagonalTailChunk001Sub001Block126HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block126HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block126Head

def SurrogateDiagonalTailChunk001Sub001Block126MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block126MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block126Mid

def SurrogateDiagonalTailChunk001Sub001Block126TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block126TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block126Tail

theorem surrogateDiagonalTailChunk001Sub001Block126_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block126HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block126MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block126TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block126Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block126 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block126HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block126MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block126TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block126Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block126_eq_head_add_mid_add_tail

/-- Block 127 covers tail-support indices [18175,18200) and q from 29942 to 29983. -/

def TailChunk001Sub001Block127Part000SupportExplicit : Finset ℕ :=
  ([29942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part000 : ℚ :=
  (6203329623 : ℚ) / 1140568121344000000

def SurrogateDiagonalTailChunk001Sub001Block127Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29942
    = surrogateDiagTailX0RatChunk001Sub001Block127Part000

theorem surrogateDiagonalTailChunk001Sub001Block127Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part000] using hcert

def TailChunk001Sub001Block127Part001SupportExplicit : Finset ℕ :=
  ([29945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part001 : ℚ :=
  (193796368125 : ℚ) / 61372108388008198144

def SurrogateDiagonalTailChunk001Sub001Block127Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29945
    = surrogateDiagTailX0RatChunk001Sub001Block127Part001

theorem surrogateDiagonalTailChunk001Sub001Block127Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part001] using hcert

def TailChunk001Sub001Block127Part002SupportExplicit : Finset ℕ :=
  ([29946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part002 : ℚ :=
  (6977359313 : ℚ) / 43726535302348800

def SurrogateDiagonalTailChunk001Sub001Block127Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29946
    = surrogateDiagTailX0RatChunk001Sub001Block127Part002

theorem surrogateDiagonalTailChunk001Sub001Block127Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part002] using hcert

def TailChunk001Sub001Block127Part003SupportExplicit : Finset ℕ :=
  ([29947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block127Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29947
    = surrogateDiagTailX0RatChunk001Sub001Block127Part003

theorem surrogateDiagonalTailChunk001Sub001Block127Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part003] using hcert

def TailChunk001Sub001Block127Part004SupportExplicit : Finset ℕ :=
  ([29949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part004 : ℚ :=
  (16649802425 : ℚ) / 45528092849325182976

def SurrogateDiagonalTailChunk001Sub001Block127Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29949
    = surrogateDiagTailX0RatChunk001Sub001Block127Part004

theorem surrogateDiagonalTailChunk001Sub001Block127Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part004] using hcert

def TailChunk001Sub001Block127Part005SupportExplicit : Finset ℕ :=
  ([29951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part005 : ℚ :=
  (1123677349 : ℚ) / 12454460554032000000

def SurrogateDiagonalTailChunk001Sub001Block127Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29951
    = surrogateDiagTailX0RatChunk001Sub001Block127Part005

theorem surrogateDiagonalTailChunk001Sub001Block127Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part005] using hcert

def TailChunk001Sub001Block127Part006SupportExplicit : Finset ℕ :=
  ([29953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part006 : ℚ :=
  (26622090043 : ℚ) / 7344441277800652800

def SurrogateDiagonalTailChunk001Sub001Block127Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29953
    = surrogateDiagTailX0RatChunk001Sub001Block127Part006

theorem surrogateDiagonalTailChunk001Sub001Block127Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part006] using hcert

def TailChunk001Sub001Block127Part007SupportExplicit : Finset ℕ :=
  ([29954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part007 : ℚ :=
  (178853343 : ℚ) / 59559841575731200

def SurrogateDiagonalTailChunk001Sub001Block127Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29954
    = surrogateDiagTailX0RatChunk001Sub001Block127Part007

theorem surrogateDiagonalTailChunk001Sub001Block127Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part007] using hcert

def TailChunk001Sub001Block127Part008SupportExplicit : Finset ℕ :=
  ([29955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part008 : ℚ :=
  (623852480675 : ℚ) / 81282856780562694144

def SurrogateDiagonalTailChunk001Sub001Block127Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29955
    = surrogateDiagTailX0RatChunk001Sub001Block127Part008

theorem surrogateDiagonalTailChunk001Sub001Block127Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part008] using hcert

def TailChunk001Sub001Block127Part009SupportExplicit : Finset ℕ :=
  ([29957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part009 : ℚ :=
  (1635883825 : ℚ) / 10376920551985053696

def SurrogateDiagonalTailChunk001Sub001Block127Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29957
    = surrogateDiagTailX0RatChunk001Sub001Block127Part009

theorem surrogateDiagonalTailChunk001Sub001Block127Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part009] using hcert

def TailChunk001Sub001Block127Part010SupportExplicit : Finset ℕ :=
  ([29958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part010 : ℚ :=
  (389532265675 : ℚ) / 6211337916820488192

def SurrogateDiagonalTailChunk001Sub001Block127Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29958
    = surrogateDiagTailX0RatChunk001Sub001Block127Part010

theorem surrogateDiagonalTailChunk001Sub001Block127Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part010] using hcert

def TailChunk001Sub001Block127Part011SupportExplicit : Finset ℕ :=
  ([29959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block127Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29959
    = surrogateDiagTailX0RatChunk001Sub001Block127Part011

theorem surrogateDiagonalTailChunk001Sub001Block127Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part011] using hcert

def TailChunk001Sub001Block127Part012SupportExplicit : Finset ℕ :=
  ([29962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part012 : ℚ :=
  (500543587 : ℚ) / 667203243966000000

def SurrogateDiagonalTailChunk001Sub001Block127Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29962
    = surrogateDiagTailX0RatChunk001Sub001Block127Part012

theorem surrogateDiagonalTailChunk001Sub001Block127Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part012] using hcert

def TailChunk001Sub001Block127Part013SupportExplicit : Finset ℕ :=
  ([29965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part013 : ℚ :=
  (17643598129 : ℚ) / 3962158784918323200

def SurrogateDiagonalTailChunk001Sub001Block127Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29965
    = surrogateDiagTailX0RatChunk001Sub001Block127Part013

theorem surrogateDiagonalTailChunk001Sub001Block127Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part013] using hcert

def TailChunk001Sub001Block127Part014SupportExplicit : Finset ℕ :=
  ([29966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block127Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29966
    = surrogateDiagTailX0RatChunk001Sub001Block127Part014

theorem surrogateDiagonalTailChunk001Sub001Block127Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part014] using hcert

def TailChunk001Sub001Block127Part015SupportExplicit : Finset ℕ :=
  ([29967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part015 : ℚ :=
  (3192925 : ℚ) / 893165322796416

def SurrogateDiagonalTailChunk001Sub001Block127Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29967
    = surrogateDiagTailX0RatChunk001Sub001Block127Part015

theorem surrogateDiagonalTailChunk001Sub001Block127Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part015] using hcert

def TailChunk001Sub001Block127Part016SupportExplicit : Finset ℕ :=
  ([29969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part016 : ℚ :=
  (71735312125 : ℚ) / 280549997208084719808

def SurrogateDiagonalTailChunk001Sub001Block127Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29969
    = surrogateDiagTailX0RatChunk001Sub001Block127Part016

theorem surrogateDiagonalTailChunk001Sub001Block127Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part016] using hcert

def TailChunk001Sub001Block127Part017SupportExplicit : Finset ℕ :=
  ([29971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part017 : ℚ :=
  (9335666197 : ℚ) / 13054009259379916800

def SurrogateDiagonalTailChunk001Sub001Block127Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29971
    = surrogateDiagTailX0RatChunk001Sub001Block127Part017

theorem surrogateDiagonalTailChunk001Sub001Block127Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part017] using hcert

def TailChunk001Sub001Block127Part018SupportExplicit : Finset ℕ :=
  ([29973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part018 : ℚ :=
  (122389042825 : ℚ) / 367817561414270189568

def SurrogateDiagonalTailChunk001Sub001Block127Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29973
    = surrogateDiagTailX0RatChunk001Sub001Block127Part018

theorem surrogateDiagonalTailChunk001Sub001Block127Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part018] using hcert

def TailChunk001Sub001Block127Part019SupportExplicit : Finset ℕ :=
  ([29974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part019 : ℚ :=
  (11484206087 : ℚ) / 1359305109828633600

def SurrogateDiagonalTailChunk001Sub001Block127Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29974
    = surrogateDiagTailX0RatChunk001Sub001Block127Part019

theorem surrogateDiagonalTailChunk001Sub001Block127Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part019] using hcert

def TailChunk001Sub001Block127Part020SupportExplicit : Finset ℕ :=
  ([29977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part020 : ℚ :=
  (2405910989 : ℚ) / 14109459277033088640

def SurrogateDiagonalTailChunk001Sub001Block127Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29977
    = surrogateDiagTailX0RatChunk001Sub001Block127Part020

theorem surrogateDiagonalTailChunk001Sub001Block127Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part020] using hcert

def TailChunk001Sub001Block127Part021SupportExplicit : Finset ℕ :=
  ([29978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part021 : ℚ :=
  (167665006325 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk001Sub001Block127Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29978
    = surrogateDiagTailX0RatChunk001Sub001Block127Part021

theorem surrogateDiagonalTailChunk001Sub001Block127Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part021] using hcert

def TailChunk001Sub001Block127Part022SupportExplicit : Finset ℕ :=
  ([29981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part022 : ℚ :=
  (1147845213925 : ℚ) / 1089478118802176005248

def SurrogateDiagonalTailChunk001Sub001Block127Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29981
    = surrogateDiagTailX0RatChunk001Sub001Block127Part022

theorem surrogateDiagonalTailChunk001Sub001Block127Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part022] using hcert

def TailChunk001Sub001Block127Part023SupportExplicit : Finset ℕ :=
  ([29982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part023 : ℚ :=
  (784265899175 : ℚ) / 9894914173323961344

def SurrogateDiagonalTailChunk001Sub001Block127Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29982
    = surrogateDiagTailX0RatChunk001Sub001Block127Part023

theorem surrogateDiagonalTailChunk001Sub001Block127Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part023] using hcert

def TailChunk001Sub001Block127Part024SupportExplicit : Finset ℕ :=
  ([29983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block127Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block127Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29983
    = surrogateDiagTailX0RatChunk001Sub001Block127Part024

theorem surrogateDiagonalTailChunk001Sub001Block127Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block127Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block127Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block127Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block127Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block127Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block127HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block127Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block127Part000
    + surrogateDiagTailX0RatChunk001Sub001Block127Part001
    + surrogateDiagTailX0RatChunk001Sub001Block127Part002
    + surrogateDiagTailX0RatChunk001Sub001Block127Part003
    + surrogateDiagTailX0RatChunk001Sub001Block127Part004
    + surrogateDiagTailX0RatChunk001Sub001Block127Part005
    + surrogateDiagTailX0RatChunk001Sub001Block127Part006
    + surrogateDiagTailX0RatChunk001Sub001Block127Part007
    + surrogateDiagTailX0RatChunk001Sub001Block127Part008
    + surrogateDiagTailX0RatChunk001Sub001Block127Part009

def surrogateDiagonalTailChunk001Sub001Block127MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block127Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block127Part010
    + surrogateDiagTailX0RatChunk001Sub001Block127Part011
    + surrogateDiagTailX0RatChunk001Sub001Block127Part012
    + surrogateDiagTailX0RatChunk001Sub001Block127Part013
    + surrogateDiagTailX0RatChunk001Sub001Block127Part014
    + surrogateDiagTailX0RatChunk001Sub001Block127Part015
    + surrogateDiagTailX0RatChunk001Sub001Block127Part016
    + surrogateDiagTailX0RatChunk001Sub001Block127Part017
    + surrogateDiagTailX0RatChunk001Sub001Block127Part018
    + surrogateDiagTailX0RatChunk001Sub001Block127Part019

def surrogateDiagonalTailChunk001Sub001Block127TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block127Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block127Part020
    + surrogateDiagTailX0RatChunk001Sub001Block127Part021
    + surrogateDiagTailX0RatChunk001Sub001Block127Part022
    + surrogateDiagTailX0RatChunk001Sub001Block127Part023
    + surrogateDiagTailX0RatChunk001Sub001Block127Part024

def surrogateDiagonalTailChunk001Sub001Block127Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block127HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block127MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block127TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block127 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block127Part000
    + surrogateDiagTailX0RatChunk001Sub001Block127Part001
    + surrogateDiagTailX0RatChunk001Sub001Block127Part002
    + surrogateDiagTailX0RatChunk001Sub001Block127Part003
    + surrogateDiagTailX0RatChunk001Sub001Block127Part004
    + surrogateDiagTailX0RatChunk001Sub001Block127Part005
    + surrogateDiagTailX0RatChunk001Sub001Block127Part006
    + surrogateDiagTailX0RatChunk001Sub001Block127Part007
    + surrogateDiagTailX0RatChunk001Sub001Block127Part008
    + surrogateDiagTailX0RatChunk001Sub001Block127Part009
    + surrogateDiagTailX0RatChunk001Sub001Block127Part010
    + surrogateDiagTailX0RatChunk001Sub001Block127Part011
    + surrogateDiagTailX0RatChunk001Sub001Block127Part012
    + surrogateDiagTailX0RatChunk001Sub001Block127Part013
    + surrogateDiagTailX0RatChunk001Sub001Block127Part014
    + surrogateDiagTailX0RatChunk001Sub001Block127Part015
    + surrogateDiagTailX0RatChunk001Sub001Block127Part016
    + surrogateDiagTailX0RatChunk001Sub001Block127Part017
    + surrogateDiagTailX0RatChunk001Sub001Block127Part018
    + surrogateDiagTailX0RatChunk001Sub001Block127Part019
    + surrogateDiagTailX0RatChunk001Sub001Block127Part020
    + surrogateDiagTailX0RatChunk001Sub001Block127Part021
    + surrogateDiagTailX0RatChunk001Sub001Block127Part022
    + surrogateDiagTailX0RatChunk001Sub001Block127Part023
    + surrogateDiagTailX0RatChunk001Sub001Block127Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block127_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block127Head + surrogateDiagTailX0RatChunk001Sub001Block127Mid + surrogateDiagTailX0RatChunk001Sub001Block127Tail =
      surrogateDiagTailX0RatChunk001Sub001Block127 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block127Head surrogateDiagTailX0RatChunk001Sub001Block127Mid surrogateDiagTailX0RatChunk001Sub001Block127Tail surrogateDiagTailX0RatChunk001Sub001Block127
  ring

def SurrogateDiagonalTailChunk001Sub001Block127HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block127HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block127Head

def SurrogateDiagonalTailChunk001Sub001Block127MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block127MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block127Mid

def SurrogateDiagonalTailChunk001Sub001Block127TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block127TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block127Tail

theorem surrogateDiagonalTailChunk001Sub001Block127_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block127HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block127MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block127TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block127Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block127 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block127HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block127MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block127TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block127Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block127_eq_head_add_mid_add_tail

/-- Block 128 covers tail-support indices [18200,18211) and q from 29985 to 29999. -/

def TailChunk001Sub001Block128Part000SupportExplicit : Finset ℕ :=
  ([29985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part000 : ℚ :=
  (6511466725 : ℚ) / 850095101610837504

def SurrogateDiagonalTailChunk001Sub001Block128Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29985
    = surrogateDiagTailX0RatChunk001Sub001Block128Part000

theorem surrogateDiagonalTailChunk001Sub001Block128Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part000] using hcert

def TailChunk001Sub001Block128Part001SupportExplicit : Finset ℕ :=
  ([29986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part001 : ℚ :=
  (4230991467 : ℚ) / 458774269029171200

def SurrogateDiagonalTailChunk001Sub001Block128Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29986
    = surrogateDiagTailX0RatChunk001Sub001Block128Part001

theorem surrogateDiagonalTailChunk001Sub001Block128Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part001] using hcert

def TailChunk001Sub001Block128Part002SupportExplicit : Finset ℕ :=
  ([29987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part002 : ℚ :=
  (1431384529 : ℚ) / 25732287364259174400

def SurrogateDiagonalTailChunk001Sub001Block128Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29987
    = surrogateDiagTailX0RatChunk001Sub001Block128Part002

theorem surrogateDiagonalTailChunk001Sub001Block128Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part002] using hcert

def TailChunk001Sub001Block128Part003SupportExplicit : Finset ℕ :=
  ([29989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block128Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29989
    = surrogateDiagTailX0RatChunk001Sub001Block128Part003

theorem surrogateDiagonalTailChunk001Sub001Block128Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part003] using hcert

def TailChunk001Sub001Block128Part004SupportExplicit : Finset ℕ :=
  ([29990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part004 : ℚ :=
  (1124526025225 : ℚ) / 51712238558205954048

def SurrogateDiagonalTailChunk001Sub001Block128Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29990
    = surrogateDiagTailX0RatChunk001Sub001Block128Part004

theorem surrogateDiagonalTailChunk001Sub001Block128Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part004] using hcert

def TailChunk001Sub001Block128Part005SupportExplicit : Finset ℕ :=
  ([29991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part005 : ℚ :=
  (224977641725 : ℚ) / 144306771379926073344

def SurrogateDiagonalTailChunk001Sub001Block128Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29991
    = surrogateDiagTailX0RatChunk001Sub001Block128Part005

theorem surrogateDiagonalTailChunk001Sub001Block128Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part005] using hcert

def TailChunk001Sub001Block128Part006SupportExplicit : Finset ℕ :=
  ([29993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part006 : ℚ :=
  (529500925 : ℚ) / 7584275776451641344

def SurrogateDiagonalTailChunk001Sub001Block128Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29993
    = surrogateDiagTailX0RatChunk001Sub001Block128Part006

theorem surrogateDiagonalTailChunk001Sub001Block128Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part006] using hcert

def TailChunk001Sub001Block128Part007SupportExplicit : Finset ℕ :=
  ([29994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part007 : ℚ :=
  (111562522325 : ℚ) / 1783215428457097152

def SurrogateDiagonalTailChunk001Sub001Block128Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29994
    = surrogateDiagTailX0RatChunk001Sub001Block128Part007

theorem surrogateDiagonalTailChunk001Sub001Block128Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part007] using hcert

def TailChunk001Sub001Block128Part008SupportExplicit : Finset ℕ :=
  ([29995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part008 : ℚ :=
  (35725848475 : ℚ) / 6186348588731203584

def SurrogateDiagonalTailChunk001Sub001Block128Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29995
    = surrogateDiagTailX0RatChunk001Sub001Block128Part008

theorem surrogateDiagonalTailChunk001Sub001Block128Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part008] using hcert

def TailChunk001Sub001Block128Part009SupportExplicit : Finset ℕ :=
  ([29998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part009 : ℚ :=
  (13189682525 : ℚ) / 14452623184818514176

def SurrogateDiagonalTailChunk001Sub001Block128Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29998
    = surrogateDiagTailX0RatChunk001Sub001Block128Part009

theorem surrogateDiagonalTailChunk001Sub001Block128Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part009] using hcert

def TailChunk001Sub001Block128Part010SupportExplicit : Finset ℕ :=
  ([29999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block128Part010 : ℚ :=
  (2232646391 : ℚ) / 38598431046388761600

def SurrogateDiagonalTailChunk001Sub001Block128Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 29999
    = surrogateDiagTailX0RatChunk001Sub001Block128Part010

theorem surrogateDiagonalTailChunk001Sub001Block128Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block128Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block128Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block128Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block128Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block128Part010] using hcert

def surrogateDiagonalTailChunk001Sub001Block128HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block128Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block128Part000
    + surrogateDiagTailX0RatChunk001Sub001Block128Part001
    + surrogateDiagTailX0RatChunk001Sub001Block128Part002
    + surrogateDiagTailX0RatChunk001Sub001Block128Part003
    + surrogateDiagTailX0RatChunk001Sub001Block128Part004
    + surrogateDiagTailX0RatChunk001Sub001Block128Part005
    + surrogateDiagTailX0RatChunk001Sub001Block128Part006
    + surrogateDiagTailX0RatChunk001Sub001Block128Part007
    + surrogateDiagTailX0RatChunk001Sub001Block128Part008
    + surrogateDiagTailX0RatChunk001Sub001Block128Part009

def surrogateDiagonalTailChunk001Sub001Block128MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block128Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block128Part010

def surrogateDiagonalTailChunk001Sub001Block128TailSum (X0 : ℕ) : ℚ := (0 : ℚ)

def surrogateDiagTailX0RatChunk001Sub001Block128Tail : ℚ := (0 : ℚ)

def surrogateDiagonalTailChunk001Sub001Block128Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block128HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block128MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block128TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block128 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block128Part000
    + surrogateDiagTailX0RatChunk001Sub001Block128Part001
    + surrogateDiagTailX0RatChunk001Sub001Block128Part002
    + surrogateDiagTailX0RatChunk001Sub001Block128Part003
    + surrogateDiagTailX0RatChunk001Sub001Block128Part004
    + surrogateDiagTailX0RatChunk001Sub001Block128Part005
    + surrogateDiagTailX0RatChunk001Sub001Block128Part006
    + surrogateDiagTailX0RatChunk001Sub001Block128Part007
    + surrogateDiagTailX0RatChunk001Sub001Block128Part008
    + surrogateDiagTailX0RatChunk001Sub001Block128Part009
    + surrogateDiagTailX0RatChunk001Sub001Block128Part010

theorem surrogateDiagTailX0RatChunk001Sub001Block128_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block128Head + surrogateDiagTailX0RatChunk001Sub001Block128Mid + surrogateDiagTailX0RatChunk001Sub001Block128Tail =
      surrogateDiagTailX0RatChunk001Sub001Block128 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block128Head surrogateDiagTailX0RatChunk001Sub001Block128Mid surrogateDiagTailX0RatChunk001Sub001Block128Tail surrogateDiagTailX0RatChunk001Sub001Block128
  ring

def SurrogateDiagonalTailChunk001Sub001Block128HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block128HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block128Head

def SurrogateDiagonalTailChunk001Sub001Block128MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block128MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block128Mid

def SurrogateDiagonalTailChunk001Sub001Block128TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block128TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block128Tail

theorem surrogateDiagonalTailChunk001Sub001Block128_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block128HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block128MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block128TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block128Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block128 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block128HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block128MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block128TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block128Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block128_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
