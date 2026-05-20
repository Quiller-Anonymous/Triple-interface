import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [192,193). -/

/-- Block 192 covers tail-support indices [4800,4825) and q from 7945 to 7985. -/

def TailChunk000Sub000Block192Part000SupportExplicit : Finset ℕ :=
  ([7945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part000 : ℚ :=
  (570158502625 : ℚ) / 541060202833846272

def SurrogateDiagonalTailChunk000Sub000Block192Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7945
    = surrogateDiagTailX0RatChunk000Sub000Block192Part000

theorem surrogateDiagonalTailChunk000Sub000Block192Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part000] using hcert

def TailChunk000Sub000Block192Part001SupportExplicit : Finset ℕ :=
  ([7946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part001 : ℚ :=
  (109527386075 : ℚ) / 30928987023212544

def SurrogateDiagonalTailChunk000Sub000Block192Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7946
    = surrogateDiagTailX0RatChunk000Sub000Block192Part001

theorem surrogateDiagonalTailChunk000Sub000Block192Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part001] using hcert

def TailChunk000Sub000Block192Part002SupportExplicit : Finset ℕ :=
  ([7949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part002 : ℚ :=
  (987290640625 : ℚ) / 2494584969640241952

def SurrogateDiagonalTailChunk000Sub000Block192Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7949
    = surrogateDiagTailX0RatChunk000Sub000Block192Part002

theorem surrogateDiagonalTailChunk000Sub000Block192Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part002] using hcert

def TailChunk000Sub000Block192Part003SupportExplicit : Finset ℕ :=
  ([7951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part003 : ℚ :=
  (63218401 : ℚ) / 159814196698050

def SurrogateDiagonalTailChunk000Sub000Block192Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7951
    = surrogateDiagTailX0RatChunk000Sub000Block192Part003

theorem surrogateDiagonalTailChunk000Sub000Block192Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part003] using hcert

def TailChunk000Sub000Block192Part004SupportExplicit : Finset ℕ :=
  ([7953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part004 : ℚ :=
  (2873672801 : ℚ) / 1966473216000000

def SurrogateDiagonalTailChunk000Sub000Block192Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7953
    = surrogateDiagTailX0RatChunk000Sub000Block192Part004

theorem surrogateDiagonalTailChunk000Sub000Block192Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part004] using hcert

def TailChunk000Sub000Block192Part005SupportExplicit : Finset ℕ :=
  ([7954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part005 : ℚ :=
  (1284741557 : ℚ) / 724920686346240

def SurrogateDiagonalTailChunk000Sub000Block192Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7954
    = surrogateDiagTailX0RatChunk000Sub000Block192Part005

theorem surrogateDiagonalTailChunk000Sub000Block192Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part005] using hcert

def TailChunk000Sub000Block192Part006SupportExplicit : Finset ℕ :=
  ([7955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part006 : ℚ :=
  (95169055075 : ℚ) / 119485706962599936

def SurrogateDiagonalTailChunk000Sub000Block192Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7955
    = surrogateDiagTailX0RatChunk000Sub000Block192Part006

theorem surrogateDiagonalTailChunk000Sub000Block192Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part006] using hcert

def TailChunk000Sub000Block192Part007SupportExplicit : Finset ℕ :=
  ([7957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part007 : ℚ :=
  (958652571475 : ℚ) / 2285556044844367872

def SurrogateDiagonalTailChunk000Sub000Block192Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7957
    = surrogateDiagTailX0RatChunk000Sub000Block192Part007

theorem surrogateDiagonalTailChunk000Sub000Block192Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part007] using hcert

def TailChunk000Sub000Block192Part008SupportExplicit : Finset ℕ :=
  ([7958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part008 : ℚ :=
  (476848372025 : ℚ) / 256331143035331584

def SurrogateDiagonalTailChunk000Sub000Block192Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7958
    = surrogateDiagTailX0RatChunk000Sub000Block192Part008

theorem surrogateDiagonalTailChunk000Sub000Block192Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part008] using hcert

def TailChunk000Sub000Block192Part009SupportExplicit : Finset ℕ :=
  ([7959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part009 : ℚ :=
  (259556480725 : ℚ) / 151224097874540544

def SurrogateDiagonalTailChunk000Sub000Block192Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7959
    = surrogateDiagTailX0RatChunk000Sub000Block192Part009

theorem surrogateDiagonalTailChunk000Sub000Block192Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part009] using hcert

def TailChunk000Sub000Block192Part010SupportExplicit : Finset ℕ :=
  ([7961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part010 : ℚ :=
  (1221503213275 : ℚ) / 2671165222095655296

def SurrogateDiagonalTailChunk000Sub000Block192Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7961
    = surrogateDiagTailX0RatChunk000Sub000Block192Part010

theorem surrogateDiagonalTailChunk000Sub000Block192Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part010] using hcert

def TailChunk000Sub000Block192Part011SupportExplicit : Finset ℕ :=
  ([7962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part011 : ℚ :=
  (770002399975 : ℚ) / 123686111962977408

def SurrogateDiagonalTailChunk000Sub000Block192Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7962
    = surrogateDiagTailX0RatChunk000Sub000Block192Part011

theorem surrogateDiagonalTailChunk000Sub000Block192Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part011] using hcert

def TailChunk000Sub000Block192Part012SupportExplicit : Finset ℕ :=
  ([7963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part012 : ℚ :=
  (990771390625 : ℚ) / 2512207804955982642

def SurrogateDiagonalTailChunk000Sub000Block192Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7963
    = surrogateDiagTailX0RatChunk000Sub000Block192Part012

theorem surrogateDiagonalTailChunk000Sub000Block192Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part012] using hcert

def TailChunk000Sub000Block192Part013SupportExplicit : Finset ℕ :=
  ([7966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part013 : ℚ :=
  (889249402225 : ℚ) / 337306882905243648

def SurrogateDiagonalTailChunk000Sub000Block192Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7966
    = surrogateDiagTailX0RatChunk000Sub000Block192Part013

theorem surrogateDiagonalTailChunk000Sub000Block192Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part013] using hcert

def TailChunk000Sub000Block192Part014SupportExplicit : Finset ℕ :=
  ([7967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part014 : ℚ :=
  (150802544017 : ℚ) / 347961929446195200

def SurrogateDiagonalTailChunk000Sub000Block192Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7967
    = surrogateDiagTailX0RatChunk000Sub000Block192Part014

theorem surrogateDiagonalTailChunk000Sub000Block192Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part014] using hcert

def TailChunk000Sub000Block192Part015SupportExplicit : Finset ℕ :=
  ([7969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part015 : ℚ :=
  (27649169075 : ℚ) / 56826062153922816

def SurrogateDiagonalTailChunk000Sub000Block192Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7969
    = surrogateDiagTailX0RatChunk000Sub000Block192Part015

theorem surrogateDiagonalTailChunk000Sub000Block192Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part015] using hcert

def TailChunk000Sub000Block192Part016SupportExplicit : Finset ℕ :=
  ([7970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part016 : ℚ :=
  (277676413875 : ℚ) / 85663899584659456

def SurrogateDiagonalTailChunk000Sub000Block192Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7970
    = surrogateDiagTailX0RatChunk000Sub000Block192Part016

theorem surrogateDiagonalTailChunk000Sub000Block192Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part016] using hcert

def TailChunk000Sub000Block192Part017SupportExplicit : Finset ℕ :=
  ([7971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part017 : ℚ :=
  (1102728793925 : ℚ) / 995472182643523584

def SurrogateDiagonalTailChunk000Sub000Block192Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7971
    = surrogateDiagTailX0RatChunk000Sub000Block192Part017

theorem surrogateDiagonalTailChunk000Sub000Block192Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part017] using hcert

def TailChunk000Sub000Block192Part018SupportExplicit : Finset ℕ :=
  ([7973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part018 : ℚ :=
  (974159873275 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub000Block192Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7973
    = surrogateDiagTailX0RatChunk000Sub000Block192Part018

theorem surrogateDiagonalTailChunk000Sub000Block192Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part018] using hcert

def TailChunk000Sub000Block192Part019SupportExplicit : Finset ℕ :=
  ([7977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part019 : ℚ :=
  (1766865734125 : ℚ) / 1996947962582410368

def SurrogateDiagonalTailChunk000Sub000Block192Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7977
    = surrogateDiagTailX0RatChunk000Sub000Block192Part019

theorem surrogateDiagonalTailChunk000Sub000Block192Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part019] using hcert

def TailChunk000Sub000Block192Part020SupportExplicit : Finset ℕ :=
  ([7978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part020 : ℚ :=
  (248626890625 : ℚ) / 158120240457506592

def SurrogateDiagonalTailChunk000Sub000Block192Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7978
    = surrogateDiagTailX0RatChunk000Sub000Block192Part020

theorem surrogateDiagonalTailChunk000Sub000Block192Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part020] using hcert

def TailChunk000Sub000Block192Part021SupportExplicit : Finset ℕ :=
  ([7979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part021 : ℚ :=
  (38576684611 : ℚ) / 92556147528000000

def SurrogateDiagonalTailChunk000Sub000Block192Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7979
    = surrogateDiagTailX0RatChunk000Sub000Block192Part021

theorem surrogateDiagonalTailChunk000Sub000Block192Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part021] using hcert

def TailChunk000Sub000Block192Part022SupportExplicit : Finset ℕ :=
  ([7981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part022 : ℚ :=
  (3733642201075 : ℚ) / 8395024682182435968

def SurrogateDiagonalTailChunk000Sub000Block192Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7981
    = surrogateDiagTailX0RatChunk000Sub000Block192Part022

theorem surrogateDiagonalTailChunk000Sub000Block192Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part022] using hcert

def TailChunk000Sub000Block192Part023SupportExplicit : Finset ℕ :=
  ([7982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part023 : ℚ :=
  (467213733725 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub000Block192Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7982
    = surrogateDiagTailX0RatChunk000Sub000Block192Part023

theorem surrogateDiagonalTailChunk000Sub000Block192Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part023] using hcert

def TailChunk000Sub000Block192Part024SupportExplicit : Finset ℕ :=
  ([7985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block192Part024 : ℚ :=
  (409616292475 : ℚ) / 593335498288103424

def SurrogateDiagonalTailChunk000Sub000Block192Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7985
    = surrogateDiagTailX0RatChunk000Sub000Block192Part024

theorem surrogateDiagonalTailChunk000Sub000Block192Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block192Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block192Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block192Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block192Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block192Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block192HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block192Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block192Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part000
    + surrogateDiagTailX0RatChunk000Sub000Block192Part001
    + surrogateDiagTailX0RatChunk000Sub000Block192Part002
    + surrogateDiagTailX0RatChunk000Sub000Block192Part003
    + surrogateDiagTailX0RatChunk000Sub000Block192Part004
    + surrogateDiagTailX0RatChunk000Sub000Block192Part005
    + surrogateDiagTailX0RatChunk000Sub000Block192Part006
    + surrogateDiagTailX0RatChunk000Sub000Block192Part007
    + surrogateDiagTailX0RatChunk000Sub000Block192Part008
    + surrogateDiagTailX0RatChunk000Sub000Block192Part009

def surrogateDiagonalTailChunk000Sub000Block192MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block192Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block192Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part010
    + surrogateDiagTailX0RatChunk000Sub000Block192Part011
    + surrogateDiagTailX0RatChunk000Sub000Block192Part012
    + surrogateDiagTailX0RatChunk000Sub000Block192Part013
    + surrogateDiagTailX0RatChunk000Sub000Block192Part014
    + surrogateDiagTailX0RatChunk000Sub000Block192Part015
    + surrogateDiagTailX0RatChunk000Sub000Block192Part016
    + surrogateDiagTailX0RatChunk000Sub000Block192Part017
    + surrogateDiagTailX0RatChunk000Sub000Block192Part018
    + surrogateDiagTailX0RatChunk000Sub000Block192Part019

def surrogateDiagonalTailChunk000Sub000Block192TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block192Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block192Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block192Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part020
    + surrogateDiagTailX0RatChunk000Sub000Block192Part021
    + surrogateDiagTailX0RatChunk000Sub000Block192Part022
    + surrogateDiagTailX0RatChunk000Sub000Block192Part023
    + surrogateDiagTailX0RatChunk000Sub000Block192Part024

def surrogateDiagonalTailChunk000Sub000Block192Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block192HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block192MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block192TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block192 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block192Part000
    + surrogateDiagTailX0RatChunk000Sub000Block192Part001
    + surrogateDiagTailX0RatChunk000Sub000Block192Part002
    + surrogateDiagTailX0RatChunk000Sub000Block192Part003
    + surrogateDiagTailX0RatChunk000Sub000Block192Part004
    + surrogateDiagTailX0RatChunk000Sub000Block192Part005
    + surrogateDiagTailX0RatChunk000Sub000Block192Part006
    + surrogateDiagTailX0RatChunk000Sub000Block192Part007
    + surrogateDiagTailX0RatChunk000Sub000Block192Part008
    + surrogateDiagTailX0RatChunk000Sub000Block192Part009
    + surrogateDiagTailX0RatChunk000Sub000Block192Part010
    + surrogateDiagTailX0RatChunk000Sub000Block192Part011
    + surrogateDiagTailX0RatChunk000Sub000Block192Part012
    + surrogateDiagTailX0RatChunk000Sub000Block192Part013
    + surrogateDiagTailX0RatChunk000Sub000Block192Part014
    + surrogateDiagTailX0RatChunk000Sub000Block192Part015
    + surrogateDiagTailX0RatChunk000Sub000Block192Part016
    + surrogateDiagTailX0RatChunk000Sub000Block192Part017
    + surrogateDiagTailX0RatChunk000Sub000Block192Part018
    + surrogateDiagTailX0RatChunk000Sub000Block192Part019
    + surrogateDiagTailX0RatChunk000Sub000Block192Part020
    + surrogateDiagTailX0RatChunk000Sub000Block192Part021
    + surrogateDiagTailX0RatChunk000Sub000Block192Part022
    + surrogateDiagTailX0RatChunk000Sub000Block192Part023
    + surrogateDiagTailX0RatChunk000Sub000Block192Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block192_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block192Head + surrogateDiagTailX0RatChunk000Sub000Block192Mid + surrogateDiagTailX0RatChunk000Sub000Block192Tail =
      surrogateDiagTailX0RatChunk000Sub000Block192 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block192Head surrogateDiagTailX0RatChunk000Sub000Block192Mid surrogateDiagTailX0RatChunk000Sub000Block192Tail surrogateDiagTailX0RatChunk000Sub000Block192
  ring

def SurrogateDiagonalTailChunk000Sub000Block192HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block192HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block192Head

def SurrogateDiagonalTailChunk000Sub000Block192MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block192MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block192Mid

def SurrogateDiagonalTailChunk000Sub000Block192TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block192TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block192Tail

theorem surrogateDiagonalTailChunk000Sub000Block192_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block192HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block192MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block192TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block192Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block192 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block192HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block192MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block192TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block192Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block192_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
