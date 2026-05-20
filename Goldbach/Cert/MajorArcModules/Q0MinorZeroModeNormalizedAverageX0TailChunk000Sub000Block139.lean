import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [139,140). -/

/- Block 139 covers tail-support indices [3475,3500) and q from 5771 to 5810. -/

def TailChunk000Sub000Block139Part000SupportExplicit : Finset ℕ :=
  ([5771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part000 : ℚ :=
  (994435413875 : ℚ) / 1181108376685569024

def SurrogateDiagonalTailChunk000Sub000Block139Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5771
    = surrogateDiagTailX0RatChunk000Sub000Block139Part000

theorem surrogateDiagonalTailChunk000Sub000Block139Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part000] using hcert

def TailChunk000Sub000Block139Part001SupportExplicit : Finset ℕ :=
  ([5773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part001 : ℚ :=
  (26242001019 : ℚ) / 30508183750000000

def SurrogateDiagonalTailChunk000Sub000Block139Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5773
    = surrogateDiagTailX0RatChunk000Sub000Block139Part001

theorem surrogateDiagonalTailChunk000Sub000Block139Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part001] using hcert

def TailChunk000Sub000Block139Part002SupportExplicit : Finset ℕ :=
  ([5774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part002 : ℚ :=
  (130230765625 : ℚ) / 43366280501806002

def SurrogateDiagonalTailChunk000Sub000Block139Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5774
    = surrogateDiagTailX0RatChunk000Sub000Block139Part002

theorem surrogateDiagonalTailChunk000Sub000Block139Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part002] using hcert

def TailChunk000Sub000Block139Part003SupportExplicit : Finset ℕ :=
  ([5777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part003 : ℚ :=
  (336768035275 : ℚ) / 414556763430371328

def SurrogateDiagonalTailChunk000Sub000Block139Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5777
    = surrogateDiagTailX0RatChunk000Sub000Block139Part003

theorem surrogateDiagonalTailChunk000Sub000Block139Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part003] using hcert

def TailChunk000Sub000Block139Part004SupportExplicit : Finset ℕ :=
  ([5779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part004 : ℚ :=
  (521825640625 : ℚ) / 696750064498880082

def SurrogateDiagonalTailChunk000Sub000Block139Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5779
    = surrogateDiagTailX0RatChunk000Sub000Block139Part004

theorem surrogateDiagonalTailChunk000Sub000Block139Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part004] using hcert

def TailChunk000Sub000Block139Part005SupportExplicit : Finset ℕ :=
  ([5781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part005 : ℚ :=
  (17615632149 : ℚ) / 6114442569318400

def SurrogateDiagonalTailChunk000Sub000Block139Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5781
    = surrogateDiagTailX0RatChunk000Sub000Block139Part005

theorem surrogateDiagonalTailChunk000Sub000Block139Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part005] using hcert

def TailChunk000Sub000Block139Part006SupportExplicit : Finset ℕ :=
  ([5783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part006 : ℚ :=
  (522548265625 : ℚ) / 698681456451230322

def SurrogateDiagonalTailChunk000Sub000Block139Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5783
    = surrogateDiagTailX0RatChunk000Sub000Block139Part006

theorem surrogateDiagonalTailChunk000Sub000Block139Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part006] using hcert

def TailChunk000Sub000Block139Part007SupportExplicit : Finset ℕ :=
  ([5785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part007 : ℚ :=
  (89848257025 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block139Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5785
    = surrogateDiagTailX0RatChunk000Sub000Block139Part007

theorem surrogateDiagonalTailChunk000Sub000Block139Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part007] using hcert

def TailChunk000Sub000Block139Part008SupportExplicit : Finset ℕ :=
  ([5786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part008 : ℚ :=
  (4671388397 : ℚ) / 589117641968400

def SurrogateDiagonalTailChunk000Sub000Block139Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5786
    = surrogateDiagTailX0RatChunk000Sub000Block139Part008

theorem surrogateDiagonalTailChunk000Sub000Block139Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part008] using hcert

def TailChunk000Sub000Block139Part009SupportExplicit : Finset ℕ :=
  ([5789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part009 : ℚ :=
  (1750545554575 : ℚ) / 1508523394520274048

def SurrogateDiagonalTailChunk000Sub000Block139Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5789
    = surrogateDiagTailX0RatChunk000Sub000Block139Part009

theorem surrogateDiagonalTailChunk000Sub000Block139Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part009] using hcert

def TailChunk000Sub000Block139Part010SupportExplicit : Finset ℕ :=
  ([5790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part010 : ℚ :=
  (252425903825 : ℚ) / 6959238588923904

def SurrogateDiagonalTailChunk000Sub000Block139Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5790
    = surrogateDiagTailX0RatChunk000Sub000Block139Part010

theorem surrogateDiagonalTailChunk000Sub000Block139Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part010] using hcert

def TailChunk000Sub000Block139Part011SupportExplicit : Finset ℕ :=
  ([5791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part011 : ℚ :=
  (838392025 : ℚ) / 1124090053866162

def SurrogateDiagonalTailChunk000Sub000Block139Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5791
    = surrogateDiagTailX0RatChunk000Sub000Block139Part011

theorem surrogateDiagonalTailChunk000Sub000Block139Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part011] using hcert

def TailChunk000Sub000Block139Part012SupportExplicit : Finset ℕ :=
  ([5793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part012 : ℚ :=
  (5589849 : ℚ) / 2219980801600

def SurrogateDiagonalTailChunk000Sub000Block139Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5793
    = surrogateDiagTailX0RatChunk000Sub000Block139Part012

theorem surrogateDiagonalTailChunk000Sub000Block139Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part012] using hcert

def TailChunk000Sub000Block139Part013SupportExplicit : Finset ℕ :=
  ([5794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part013 : ℚ :=
  (1048866309775 : ℚ) / 175881875885948928

def SurrogateDiagonalTailChunk000Sub000Block139Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5794
    = surrogateDiagTailX0RatChunk000Sub000Block139Part013

theorem surrogateDiagonalTailChunk000Sub000Block139Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part013] using hcert

def TailChunk000Sub000Block139Part014SupportExplicit : Finset ℕ :=
  ([5795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part014 : ℚ :=
  (59018015941 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block139Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5795
    = surrogateDiagTailX0RatChunk000Sub000Block139Part014

theorem surrogateDiagonalTailChunk000Sub000Block139Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part014] using hcert

def TailChunk000Sub000Block139Part015SupportExplicit : Finset ℕ :=
  ([5797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part015 : ℚ :=
  (3398803607 : ℚ) / 2654738841600000

def SurrogateDiagonalTailChunk000Sub000Block139Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5797
    = surrogateDiagTailX0RatChunk000Sub000Block139Part015

theorem surrogateDiagonalTailChunk000Sub000Block139Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part015] using hcert

def TailChunk000Sub000Block139Part016SupportExplicit : Finset ℕ :=
  ([5798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part016 : ℚ :=
  (5880443725 : ℚ) / 777407500329984

def SurrogateDiagonalTailChunk000Sub000Block139Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5798
    = surrogateDiagTailX0RatChunk000Sub000Block139Part016

theorem surrogateDiagonalTailChunk000Sub000Block139Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part016] using hcert

def TailChunk000Sub000Block139Part017SupportExplicit : Finset ℕ :=
  ([5799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part017 : ℚ :=
  (952625 : ℚ) / 379115154432

def SurrogateDiagonalTailChunk000Sub000Block139Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5799
    = surrogateDiagTailX0RatChunk000Sub000Block139Part017

theorem surrogateDiagonalTailChunk000Sub000Block139Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part017] using hcert

def TailChunk000Sub000Block139Part018SupportExplicit : Finset ℕ :=
  ([5801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part018 : ℚ :=
  (33651601 : ℚ) / 45275037196800

def SurrogateDiagonalTailChunk000Sub000Block139Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5801
    = surrogateDiagTailX0RatChunk000Sub000Block139Part018

theorem surrogateDiagonalTailChunk000Sub000Block139Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part018] using hcert

def TailChunk000Sub000Block139Part019SupportExplicit : Finset ℕ :=
  ([5802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part019 : ℚ :=
  (642285932725 : ℚ) / 34838171054402688

def SurrogateDiagonalTailChunk000Sub000Block139Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5802
    = surrogateDiagTailX0RatChunk000Sub000Block139Part019

theorem surrogateDiagonalTailChunk000Sub000Block139Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part019] using hcert

def TailChunk000Sub000Block139Part020SupportExplicit : Finset ℕ :=
  ([5803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part020 : ℚ :=
  (1759023958375 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub000Block139Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5803
    = surrogateDiagTailX0RatChunk000Sub000Block139Part020

theorem surrogateDiagonalTailChunk000Sub000Block139Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part020] using hcert

def TailChunk000Sub000Block139Part021SupportExplicit : Finset ℕ :=
  ([5806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part021 : ℚ :=
  (131678265625 : ℚ) / 44335999134751602

def SurrogateDiagonalTailChunk000Sub000Block139Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5806
    = surrogateDiagTailX0RatChunk000Sub000Block139Part021

theorem surrogateDiagonalTailChunk000Sub000Block139Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part021] using hcert

def TailChunk000Sub000Block139Part022SupportExplicit : Finset ℕ :=
  ([5807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block139Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5807
    = surrogateDiagTailX0RatChunk000Sub000Block139Part022

theorem surrogateDiagonalTailChunk000Sub000Block139Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part022] using hcert

def TailChunk000Sub000Block139Part023SupportExplicit : Finset ℕ :=
  ([5809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part023 : ℚ :=
  (59606352775 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub000Block139Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5809
    = surrogateDiagTailX0RatChunk000Sub000Block139Part023

theorem surrogateDiagonalTailChunk000Sub000Block139Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part023] using hcert

def TailChunk000Sub000Block139Part024SupportExplicit : Finset ℕ :=
  ([5810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block139Part024 : ℚ :=
  (57666517175 : ℚ) / 4688535927361536

def SurrogateDiagonalTailChunk000Sub000Block139Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5810
    = surrogateDiagTailX0RatChunk000Sub000Block139Part024

theorem surrogateDiagonalTailChunk000Sub000Block139Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block139Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block139Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block139Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block139Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block139Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block139Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block139HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block139Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block139Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block139Part000
    + surrogateDiagTailX0RatChunk000Sub000Block139Part001
    + surrogateDiagTailX0RatChunk000Sub000Block139Part002
    + surrogateDiagTailX0RatChunk000Sub000Block139Part003
    + surrogateDiagTailX0RatChunk000Sub000Block139Part004
    + surrogateDiagTailX0RatChunk000Sub000Block139Part005
    + surrogateDiagTailX0RatChunk000Sub000Block139Part006
    + surrogateDiagTailX0RatChunk000Sub000Block139Part007
    + surrogateDiagTailX0RatChunk000Sub000Block139Part008
    + surrogateDiagTailX0RatChunk000Sub000Block139Part009

def surrogateDiagonalTailChunk000Sub000Block139MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block139Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block139Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block139Part010
    + surrogateDiagTailX0RatChunk000Sub000Block139Part011
    + surrogateDiagTailX0RatChunk000Sub000Block139Part012
    + surrogateDiagTailX0RatChunk000Sub000Block139Part013
    + surrogateDiagTailX0RatChunk000Sub000Block139Part014
    + surrogateDiagTailX0RatChunk000Sub000Block139Part015
    + surrogateDiagTailX0RatChunk000Sub000Block139Part016
    + surrogateDiagTailX0RatChunk000Sub000Block139Part017
    + surrogateDiagTailX0RatChunk000Sub000Block139Part018
    + surrogateDiagTailX0RatChunk000Sub000Block139Part019

def surrogateDiagonalTailChunk000Sub000Block139TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block139Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block139Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block139Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block139Part020
    + surrogateDiagTailX0RatChunk000Sub000Block139Part021
    + surrogateDiagTailX0RatChunk000Sub000Block139Part022
    + surrogateDiagTailX0RatChunk000Sub000Block139Part023
    + surrogateDiagTailX0RatChunk000Sub000Block139Part024

def surrogateDiagonalTailChunk000Sub000Block139Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block139HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block139MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block139TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block139 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block139Part000
    + surrogateDiagTailX0RatChunk000Sub000Block139Part001
    + surrogateDiagTailX0RatChunk000Sub000Block139Part002
    + surrogateDiagTailX0RatChunk000Sub000Block139Part003
    + surrogateDiagTailX0RatChunk000Sub000Block139Part004
    + surrogateDiagTailX0RatChunk000Sub000Block139Part005
    + surrogateDiagTailX0RatChunk000Sub000Block139Part006
    + surrogateDiagTailX0RatChunk000Sub000Block139Part007
    + surrogateDiagTailX0RatChunk000Sub000Block139Part008
    + surrogateDiagTailX0RatChunk000Sub000Block139Part009
    + surrogateDiagTailX0RatChunk000Sub000Block139Part010
    + surrogateDiagTailX0RatChunk000Sub000Block139Part011
    + surrogateDiagTailX0RatChunk000Sub000Block139Part012
    + surrogateDiagTailX0RatChunk000Sub000Block139Part013
    + surrogateDiagTailX0RatChunk000Sub000Block139Part014
    + surrogateDiagTailX0RatChunk000Sub000Block139Part015
    + surrogateDiagTailX0RatChunk000Sub000Block139Part016
    + surrogateDiagTailX0RatChunk000Sub000Block139Part017
    + surrogateDiagTailX0RatChunk000Sub000Block139Part018
    + surrogateDiagTailX0RatChunk000Sub000Block139Part019
    + surrogateDiagTailX0RatChunk000Sub000Block139Part020
    + surrogateDiagTailX0RatChunk000Sub000Block139Part021
    + surrogateDiagTailX0RatChunk000Sub000Block139Part022
    + surrogateDiagTailX0RatChunk000Sub000Block139Part023
    + surrogateDiagTailX0RatChunk000Sub000Block139Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block139_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block139Head + surrogateDiagTailX0RatChunk000Sub000Block139Mid + surrogateDiagTailX0RatChunk000Sub000Block139Tail =
      surrogateDiagTailX0RatChunk000Sub000Block139 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block139Head surrogateDiagTailX0RatChunk000Sub000Block139Mid surrogateDiagTailX0RatChunk000Sub000Block139Tail surrogateDiagTailX0RatChunk000Sub000Block139
  ring

def SurrogateDiagonalTailChunk000Sub000Block139HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block139HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block139Head

def SurrogateDiagonalTailChunk000Sub000Block139MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block139MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block139Mid

def SurrogateDiagonalTailChunk000Sub000Block139TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block139TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block139Tail

theorem surrogateDiagonalTailChunk000Sub000Block139_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block139HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block139MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block139TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block139Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block139 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block139HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block139MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block139TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block139Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block139_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
