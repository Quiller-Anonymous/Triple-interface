import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [20,21). -/

/- Block 020 covers tail-support indices [500,525) and q from 877 to 913. -/

def TailChunk000Sub000Block020Part000SupportExplicit : Finset ℕ :=
  ([877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part000 : ℚ :=
  (120080265125 : ℚ) / 736229623201344

def SurrogateDiagonalTailChunk000Sub000Block020Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 877
    = surrogateDiagTailX0RatChunk000Sub000Block020Part000

theorem surrogateDiagonalTailChunk000Sub000Block020Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part000] using hcert

def TailChunk000Sub000Block020Part001SupportExplicit : Finset ℕ :=
  ([878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part001 : ℚ :=
  (8012375575 : ℚ) / 5112705716676

def SurrogateDiagonalTailChunk000Sub000Block020Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 878
    = surrogateDiagTailX0RatChunk000Sub000Block020Part001

theorem surrogateDiagonalTailChunk000Sub000Block020Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part001] using hcert

def TailChunk000Sub000Block020Part002SupportExplicit : Finset ℕ :=
  ([879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part002 : ℚ :=
  (187174291975 : ℚ) / 290856147437568

def SurrogateDiagonalTailChunk000Sub000Block020Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 879
    = surrogateDiagTailX0RatChunk000Sub000Block020Part002

theorem surrogateDiagonalTailChunk000Sub000Block020Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part002] using hcert

def TailChunk000Sub000Block020Part003SupportExplicit : Finset ℕ :=
  ([881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part003 : ℚ :=
  (775384839 : ℚ) / 3998768660480

def SurrogateDiagonalTailChunk000Sub000Block020Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 881
    = surrogateDiagTailX0RatChunk000Sub000Block020Part003

theorem surrogateDiagonalTailChunk000Sub000Block020Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part003] using hcert

def TailChunk000Sub000Block020Part004SupportExplicit : Finset ℕ :=
  ([883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part004 : ℚ :=
  (121728945125 : ℚ) / 756608478657444

def SurrogateDiagonalTailChunk000Sub000Block020Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 883
    = surrogateDiagTailX0RatChunk000Sub000Block020Part004

theorem surrogateDiagonalTailChunk000Sub000Block020Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part004] using hcert

def TailChunk000Sub000Block020Part005SupportExplicit : Finset ℕ :=
  ([885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part005 : ℚ :=
  (74515087775 : ℚ) / 57952047611904

def SurrogateDiagonalTailChunk000Sub000Block020Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 885
    = surrogateDiagTailX0RatChunk000Sub000Block020Part005

theorem surrogateDiagonalTailChunk000Sub000Block020Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part005] using hcert

def TailChunk000Sub000Block020Part006SupportExplicit : Finset ℕ :=
  ([886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part006 : ℚ :=
  (134651345125 : ℚ) / 95436814786248

def SurrogateDiagonalTailChunk000Sub000Block020Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 886
    = surrogateDiagTailX0RatChunk000Sub000Block020Part006

theorem surrogateDiagonalTailChunk000Sub000Block020Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part006] using hcert

def TailChunk000Sub000Block020Part007SupportExplicit : Finset ℕ :=
  ([887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part007 : ℚ :=
  (98247778875 : ℚ) / 513618303133336

def SurrogateDiagonalTailChunk000Sub000Block020Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 887
    = surrogateDiagTailX0RatChunk000Sub000Block020Part007

theorem surrogateDiagonalTailChunk000Sub000Block020Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part007] using hcert

def TailChunk000Sub000Block020Part008SupportExplicit : Finset ℕ :=
  ([889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part008 : ℚ :=
  (9221372875 : ℚ) / 30251734257024

def SurrogateDiagonalTailChunk000Sub000Block020Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 889
    = surrogateDiagTailX0RatChunk000Sub000Block020Part008

theorem surrogateDiagonalTailChunk000Sub000Block020Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part008] using hcert

def TailChunk000Sub000Block020Part009SupportExplicit : Finset ℕ :=
  ([890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part009 : ℚ :=
  (108706447975 : ℚ) / 38388179140608

def SurrogateDiagonalTailChunk000Sub000Block020Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 890
    = surrogateDiagTailX0RatChunk000Sub000Block020Part009

theorem surrogateDiagonalTailChunk000Sub000Block020Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part009] using hcert

def TailChunk000Sub000Block020Part010SupportExplicit : Finset ℕ :=
  ([893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part010 : ℚ :=
  (275866482625 : ℚ) / 1175298565350528

def SurrogateDiagonalTailChunk000Sub000Block020Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 893
    = surrogateDiagTailX0RatChunk000Sub000Block020Part010

theorem surrogateDiagonalTailChunk000Sub000Block020Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part010] using hcert

def TailChunk000Sub000Block020Part011SupportExplicit : Finset ℕ :=
  ([894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part011 : ℚ :=
  (92362128775 : ℚ) / 19195246921728

def SurrogateDiagonalTailChunk000Sub000Block020Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 894
    = surrogateDiagTailX0RatChunk000Sub000Block020Part011

theorem surrogateDiagonalTailChunk000Sub000Block020Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part011] using hcert

def TailChunk000Sub000Block020Part012SupportExplicit : Finset ℕ :=
  ([895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part012 : ℚ :=
  (78319513725 : ℚ) / 214203014649856

def SurrogateDiagonalTailChunk000Sub000Block020Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 895
    = surrogateDiagTailX0RatChunk000Sub000Block020Part012

theorem surrogateDiagonalTailChunk000Sub000Block020Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part012] using hcert

def TailChunk000Sub000Block020Part013SupportExplicit : Finset ℕ :=
  ([897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part013 : ℚ :=
  (154420450975 : ℚ) / 194340156899328

def SurrogateDiagonalTailChunk000Sub000Block020Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 897
    = surrogateDiagTailX0RatChunk000Sub000Block020Part013

theorem surrogateDiagonalTailChunk000Sub000Block020Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part013] using hcert

def TailChunk000Sub000Block020Part014SupportExplicit : Finset ℕ :=
  ([898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part014 : ℚ :=
  (138323486125 : ℚ) / 100725380087808

def SurrogateDiagonalTailChunk000Sub000Block020Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 898
    = surrogateDiagTailX0RatChunk000Sub000Block020Part014

theorem surrogateDiagonalTailChunk000Sub000Block020Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part014] using hcert

def TailChunk000Sub000Block020Part015SupportExplicit : Finset ℕ :=
  ([899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part015 : ℚ :=
  (198162247 : ℚ) / 1037439446400

def SurrogateDiagonalTailChunk000Sub000Block020Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 899
    = surrogateDiagTailX0RatChunk000Sub000Block020Part015

theorem surrogateDiagonalTailChunk000Sub000Block020Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part015] using hcert

def TailChunk000Sub000Block020Part016SupportExplicit : Finset ℕ :=
  ([901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part016 : ℚ :=
  (279575780875 : ℚ) / 1198174752473088

def SurrogateDiagonalTailChunk000Sub000Block020Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 901
    = surrogateDiagTailX0RatChunk000Sub000Block020Part016

theorem surrogateDiagonalTailChunk000Sub000Block020Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part016] using hcert

def TailChunk000Sub000Block020Part017SupportExplicit : Finset ℕ :=
  ([902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part017 : ℚ :=
  (331138647 : ℚ) / 170700800000

def SurrogateDiagonalTailChunk000Sub000Block020Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 902
    = surrogateDiagTailX0RatChunk000Sub000Block020Part017

theorem surrogateDiagonalTailChunk000Sub000Block020Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part017] using hcert

def TailChunk000Sub000Block020Part018SupportExplicit : Finset ℕ :=
  ([903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part018 : ℚ :=
  (160683476125 : ℚ) / 161342582704128

def SurrogateDiagonalTailChunk000Sub000Block020Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 903
    = surrogateDiagTailX0RatChunk000Sub000Block020Part018

theorem surrogateDiagonalTailChunk000Sub000Block020Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part018] using hcert

def TailChunk000Sub000Block020Part019SupportExplicit : Finset ℕ :=
  ([905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part019 : ℚ :=
  (9609602467 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block020Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 905
    = surrogateDiagTailX0RatChunk000Sub000Block020Part019

theorem surrogateDiagonalTailChunk000Sub000Block020Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part019] using hcert

def TailChunk000Sub000Block020Part020SupportExplicit : Finset ℕ :=
  ([906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part020 : ℚ :=
  (2307 : ℚ) / 500000

def SurrogateDiagonalTailChunk000Sub000Block020Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 906
    = surrogateDiagTailX0RatChunk000Sub000Block020Part020

theorem surrogateDiagonalTailChunk000Sub000Block020Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part020] using hcert

def TailChunk000Sub000Block020Part021SupportExplicit : Finset ℕ :=
  ([907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part021 : ℚ :=
  (128436075125 : ℚ) / 842383116554724

def SurrogateDiagonalTailChunk000Sub000Block020Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 907
    = surrogateDiagTailX0RatChunk000Sub000Block020Part021

theorem surrogateDiagonalTailChunk000Sub000Block020Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part021] using hcert

def TailChunk000Sub000Block020Part022SupportExplicit : Finset ℕ :=
  ([910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part022 : ℚ :=
  (834310925 : ℚ) / 159284330496

def SurrogateDiagonalTailChunk000Sub000Block020Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 910
    = surrogateDiagTailX0RatChunk000Sub000Block020Part022

theorem surrogateDiagonalTailChunk000Sub000Block020Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part022] using hcert

def TailChunk000Sub000Block020Part023SupportExplicit : Finset ℕ :=
  ([911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part023 : ℚ :=
  (829091079 : ℚ) / 4572578399480

def SurrogateDiagonalTailChunk000Sub000Block020Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 911
    = surrogateDiagTailX0RatChunk000Sub000Block020Part023

theorem surrogateDiagonalTailChunk000Sub000Block020Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part023] using hcert

def TailChunk000Sub000Block020Part024SupportExplicit : Finset ℕ :=
  ([913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block020Part024 : ℚ :=
  (5559660713 : ℚ) / 22610609217600

def SurrogateDiagonalTailChunk000Sub000Block020Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 913
    = surrogateDiagTailX0RatChunk000Sub000Block020Part024

theorem surrogateDiagonalTailChunk000Sub000Block020Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block020Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block020Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block020Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block020Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block020Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block020HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block020Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block020Part000
    + surrogateDiagTailX0RatChunk000Sub000Block020Part001
    + surrogateDiagTailX0RatChunk000Sub000Block020Part002
    + surrogateDiagTailX0RatChunk000Sub000Block020Part003
    + surrogateDiagTailX0RatChunk000Sub000Block020Part004
    + surrogateDiagTailX0RatChunk000Sub000Block020Part005
    + surrogateDiagTailX0RatChunk000Sub000Block020Part006
    + surrogateDiagTailX0RatChunk000Sub000Block020Part007
    + surrogateDiagTailX0RatChunk000Sub000Block020Part008
    + surrogateDiagTailX0RatChunk000Sub000Block020Part009

def surrogateDiagonalTailChunk000Sub000Block020MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block020Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block020Part010
    + surrogateDiagTailX0RatChunk000Sub000Block020Part011
    + surrogateDiagTailX0RatChunk000Sub000Block020Part012
    + surrogateDiagTailX0RatChunk000Sub000Block020Part013
    + surrogateDiagTailX0RatChunk000Sub000Block020Part014
    + surrogateDiagTailX0RatChunk000Sub000Block020Part015
    + surrogateDiagTailX0RatChunk000Sub000Block020Part016
    + surrogateDiagTailX0RatChunk000Sub000Block020Part017
    + surrogateDiagTailX0RatChunk000Sub000Block020Part018
    + surrogateDiagTailX0RatChunk000Sub000Block020Part019

def surrogateDiagonalTailChunk000Sub000Block020TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block020Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block020Part020
    + surrogateDiagTailX0RatChunk000Sub000Block020Part021
    + surrogateDiagTailX0RatChunk000Sub000Block020Part022
    + surrogateDiagTailX0RatChunk000Sub000Block020Part023
    + surrogateDiagTailX0RatChunk000Sub000Block020Part024

def surrogateDiagonalTailChunk000Sub000Block020Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block020HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block020MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block020TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block020 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block020Part000
    + surrogateDiagTailX0RatChunk000Sub000Block020Part001
    + surrogateDiagTailX0RatChunk000Sub000Block020Part002
    + surrogateDiagTailX0RatChunk000Sub000Block020Part003
    + surrogateDiagTailX0RatChunk000Sub000Block020Part004
    + surrogateDiagTailX0RatChunk000Sub000Block020Part005
    + surrogateDiagTailX0RatChunk000Sub000Block020Part006
    + surrogateDiagTailX0RatChunk000Sub000Block020Part007
    + surrogateDiagTailX0RatChunk000Sub000Block020Part008
    + surrogateDiagTailX0RatChunk000Sub000Block020Part009
    + surrogateDiagTailX0RatChunk000Sub000Block020Part010
    + surrogateDiagTailX0RatChunk000Sub000Block020Part011
    + surrogateDiagTailX0RatChunk000Sub000Block020Part012
    + surrogateDiagTailX0RatChunk000Sub000Block020Part013
    + surrogateDiagTailX0RatChunk000Sub000Block020Part014
    + surrogateDiagTailX0RatChunk000Sub000Block020Part015
    + surrogateDiagTailX0RatChunk000Sub000Block020Part016
    + surrogateDiagTailX0RatChunk000Sub000Block020Part017
    + surrogateDiagTailX0RatChunk000Sub000Block020Part018
    + surrogateDiagTailX0RatChunk000Sub000Block020Part019
    + surrogateDiagTailX0RatChunk000Sub000Block020Part020
    + surrogateDiagTailX0RatChunk000Sub000Block020Part021
    + surrogateDiagTailX0RatChunk000Sub000Block020Part022
    + surrogateDiagTailX0RatChunk000Sub000Block020Part023
    + surrogateDiagTailX0RatChunk000Sub000Block020Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block020_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block020Head + surrogateDiagTailX0RatChunk000Sub000Block020Mid + surrogateDiagTailX0RatChunk000Sub000Block020Tail =
      surrogateDiagTailX0RatChunk000Sub000Block020 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block020Head surrogateDiagTailX0RatChunk000Sub000Block020Mid surrogateDiagTailX0RatChunk000Sub000Block020Tail surrogateDiagTailX0RatChunk000Sub000Block020
  ring

def SurrogateDiagonalTailChunk000Sub000Block020HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block020HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block020Head

def SurrogateDiagonalTailChunk000Sub000Block020MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block020MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block020Mid

def SurrogateDiagonalTailChunk000Sub000Block020TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block020TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block020Tail

theorem surrogateDiagonalTailChunk000Sub000Block020_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block020HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block020MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block020TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block020Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block020 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block020HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block020MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block020TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block020Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block020_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
