import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [70,80). -/

/-- Block 070 covers tail-support indices [16750,16775) and q from 27599 to 27637. -/

def TailChunk001Sub001Block070Part000SupportExplicit : Finset ℕ :=
  ([27599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part000 : ℚ :=
  (16167506027 : ℚ) / 9394972095047270400

def SurrogateDiagonalTailChunk001Sub001Block070Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27599
    = surrogateDiagTailX0RatChunk001Sub001Block070Part000

theorem surrogateDiagonalTailChunk001Sub001Block070Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part000] using hcert

def TailChunk001Sub001Block070Part001SupportExplicit : Finset ℕ :=
  ([27601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part001 : ℚ :=
  (971953450175 : ℚ) / 391262607183745456704

def SurrogateDiagonalTailChunk001Sub001Block070Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27601
    = surrogateDiagTailX0RatChunk001Sub001Block070Part001

theorem surrogateDiagonalTailChunk001Sub001Block070Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part001] using hcert

def TailChunk001Sub001Block070Part002SupportExplicit : Finset ℕ :=
  ([27602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part002 : ℚ :=
  (61703432225 : ℚ) / 40214125211300020224

def SurrogateDiagonalTailChunk001Sub001Block070Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27602
    = surrogateDiagTailX0RatChunk001Sub001Block070Part002

theorem surrogateDiagonalTailChunk001Sub001Block070Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part002] using hcert

def TailChunk001Sub001Block070Part003SupportExplicit : Finset ℕ :=
  ([27605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part003 : ℚ :=
  (15245203979 : ℚ) / 4754590541901987840

def SurrogateDiagonalTailChunk001Sub001Block070Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27605
    = surrogateDiagTailX0RatChunk001Sub001Block070Part003

theorem surrogateDiagonalTailChunk001Sub001Block070Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part003] using hcert

def TailChunk001Sub001Block070Part004SupportExplicit : Finset ℕ :=
  ([27606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part004 : ℚ :=
  (190151789125 : ℚ) / 2245274397385979904

def SurrogateDiagonalTailChunk001Sub001Block070Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27606
    = surrogateDiagTailX0RatChunk001Sub001Block070Part004

theorem surrogateDiagonalTailChunk001Sub001Block070Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part004] using hcert

def TailChunk001Sub001Block070Part005SupportExplicit : Finset ℕ :=
  ([27607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part005 : ℚ :=
  (400771797925 : ℚ) / 1166764870626677803008

def SurrogateDiagonalTailChunk001Sub001Block070Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27607
    = surrogateDiagTailX0RatChunk001Sub001Block070Part005

theorem surrogateDiagonalTailChunk001Sub001Block070Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part005] using hcert

def TailChunk001Sub001Block070Part006SupportExplicit : Finset ℕ :=
  ([27609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part006 : ℚ :=
  (125025 : ℚ) / 57361289085235328

def SurrogateDiagonalTailChunk001Sub001Block070Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27609
    = surrogateDiagTailX0RatChunk001Sub001Block070Part006

theorem surrogateDiagonalTailChunk001Sub001Block070Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part006] using hcert

def TailChunk001Sub001Block070Part007SupportExplicit : Finset ℕ :=
  ([27610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part007 : ℚ :=
  (28313683477 : ℚ) / 1000200000000000000

def SurrogateDiagonalTailChunk001Sub001Block070Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27610
    = surrogateDiagTailX0RatChunk001Sub001Block070Part007

theorem surrogateDiagonalTailChunk001Sub001Block070Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part007] using hcert

def TailChunk001Sub001Block070Part008SupportExplicit : Finset ℕ :=
  ([27611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block070Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27611
    = surrogateDiagTailX0RatChunk001Sub001Block070Part008

theorem surrogateDiagonalTailChunk001Sub001Block070Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part008] using hcert

def TailChunk001Sub001Block070Part009SupportExplicit : Finset ℕ :=
  ([27613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part009 : ℚ :=
  (7710597 : ℚ) / 55698354663710720

def SurrogateDiagonalTailChunk001Sub001Block070Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27613
    = surrogateDiagTailX0RatChunk001Sub001Block070Part009

theorem surrogateDiagonalTailChunk001Sub001Block070Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part009] using hcert

def TailChunk001Sub001Block070Part010SupportExplicit : Finset ℕ :=
  ([27614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block070Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27614
    = surrogateDiagTailX0RatChunk001Sub001Block070Part010

theorem surrogateDiagonalTailChunk001Sub001Block070Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part010] using hcert

def TailChunk001Sub001Block070Part011SupportExplicit : Finset ℕ :=
  ([27615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part011 : ℚ :=
  (216425569775 : ℚ) / 7818203791268315136

def SurrogateDiagonalTailChunk001Sub001Block070Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27615
    = surrogateDiagTailX0RatChunk001Sub001Block070Part011

theorem surrogateDiagonalTailChunk001Sub001Block070Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part011] using hcert

def TailChunk001Sub001Block070Part012SupportExplicit : Finset ℕ :=
  ([27617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block070Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27617
    = surrogateDiagTailX0RatChunk001Sub001Block070Part012

theorem surrogateDiagonalTailChunk001Sub001Block070Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part012] using hcert

def TailChunk001Sub001Block070Part013SupportExplicit : Finset ℕ :=
  ([27618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part013 : ℚ :=
  (662137661225 : ℚ) / 8972290018928268864

def SurrogateDiagonalTailChunk001Sub001Block070Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27618
    = surrogateDiagTailX0RatChunk001Sub001Block070Part013

theorem surrogateDiagonalTailChunk001Sub001Block070Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part013] using hcert

def TailChunk001Sub001Block070Part014SupportExplicit : Finset ℕ :=
  ([27619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part014 : ℚ :=
  (5750997157 : ℚ) / 54425936753084467200

def SurrogateDiagonalTailChunk001Sub001Block070Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27619
    = surrogateDiagTailX0RatChunk001Sub001Block070Part014

theorem surrogateDiagonalTailChunk001Sub001Block070Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part014] using hcert

def TailChunk001Sub001Block070Part015SupportExplicit : Finset ℕ :=
  ([27622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part015 : ℚ :=
  (243937783175 : ℚ) / 24503578153506284544

def SurrogateDiagonalTailChunk001Sub001Block070Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27622
    = surrogateDiagTailX0RatChunk001Sub001Block070Part015

theorem surrogateDiagonalTailChunk001Sub001Block070Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part015] using hcert

def TailChunk001Sub001Block070Part016SupportExplicit : Finset ℕ :=
  ([27623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part016 : ℚ :=
  (222211571 : ℚ) / 736136957952000000

def SurrogateDiagonalTailChunk001Sub001Block070Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27623
    = surrogateDiagTailX0RatChunk001Sub001Block070Part016

theorem surrogateDiagonalTailChunk001Sub001Block070Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part016] using hcert

def TailChunk001Sub001Block070Part017SupportExplicit : Finset ℕ :=
  ([27626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part017 : ℚ :=
  (26215690625 : ℚ) / 8102533823796373632

def SurrogateDiagonalTailChunk001Sub001Block070Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27626
    = surrogateDiagTailX0RatChunk001Sub001Block070Part017

theorem surrogateDiagonalTailChunk001Sub001Block070Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part017] using hcert

def TailChunk001Sub001Block070Part018SupportExplicit : Finset ℕ :=
  ([27627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part018 : ℚ :=
  (125025 : ℚ) / 57511041092845568

def SurrogateDiagonalTailChunk001Sub001Block070Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27627
    = surrogateDiagTailX0RatChunk001Sub001Block070Part018

theorem surrogateDiagonalTailChunk001Sub001Block070Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part018] using hcert

def TailChunk001Sub001Block070Part019SupportExplicit : Finset ℕ :=
  ([27629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part019 : ℚ :=
  (975057197125 : ℚ) / 785706207075592668288

def SurrogateDiagonalTailChunk001Sub001Block070Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27629
    = surrogateDiagTailX0RatChunk001Sub001Block070Part019

theorem surrogateDiagonalTailChunk001Sub001Block070Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part019] using hcert

def TailChunk001Sub001Block070Part020SupportExplicit : Finset ℕ :=
  ([27631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block070Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27631
    = surrogateDiagTailX0RatChunk001Sub001Block070Part020

theorem surrogateDiagonalTailChunk001Sub001Block070Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part020] using hcert

def TailChunk001Sub001Block070Part021SupportExplicit : Finset ℕ :=
  ([27633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part021 : ℚ :=
  (2602485713 : ℚ) / 5249849760000000000

def SurrogateDiagonalTailChunk001Sub001Block070Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27633
    = surrogateDiagTailX0RatChunk001Sub001Block070Part021

theorem surrogateDiagonalTailChunk001Sub001Block070Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part021] using hcert

def TailChunk001Sub001Block070Part022SupportExplicit : Finset ℕ :=
  ([27634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part022 : ℚ :=
  (73780081 : ℚ) / 50992223669452800

def SurrogateDiagonalTailChunk001Sub001Block070Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27634
    = surrogateDiagTailX0RatChunk001Sub001Block070Part022

theorem surrogateDiagonalTailChunk001Sub001Block070Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part022] using hcert

def TailChunk001Sub001Block070Part023SupportExplicit : Finset ℕ :=
  ([27635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part023 : ℚ :=
  (1909792746625 : ℚ) / 596912050460929148928

def SurrogateDiagonalTailChunk001Sub001Block070Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27635
    = surrogateDiagTailX0RatChunk001Sub001Block070Part023

theorem surrogateDiagonalTailChunk001Sub001Block070Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part023] using hcert

def TailChunk001Sub001Block070Part024SupportExplicit : Finset ℕ :=
  ([27637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block070Part024 : ℚ :=
  (24310468425 : ℚ) / 105202371943872200704

def SurrogateDiagonalTailChunk001Sub001Block070Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27637
    = surrogateDiagTailX0RatChunk001Sub001Block070Part024

theorem surrogateDiagonalTailChunk001Sub001Block070Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block070Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block070Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block070Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block070Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block070Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block070HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block070Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block070Part000
    + surrogateDiagTailX0RatChunk001Sub001Block070Part001
    + surrogateDiagTailX0RatChunk001Sub001Block070Part002
    + surrogateDiagTailX0RatChunk001Sub001Block070Part003
    + surrogateDiagTailX0RatChunk001Sub001Block070Part004
    + surrogateDiagTailX0RatChunk001Sub001Block070Part005
    + surrogateDiagTailX0RatChunk001Sub001Block070Part006
    + surrogateDiagTailX0RatChunk001Sub001Block070Part007
    + surrogateDiagTailX0RatChunk001Sub001Block070Part008
    + surrogateDiagTailX0RatChunk001Sub001Block070Part009

def surrogateDiagonalTailChunk001Sub001Block070MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block070Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block070Part010
    + surrogateDiagTailX0RatChunk001Sub001Block070Part011
    + surrogateDiagTailX0RatChunk001Sub001Block070Part012
    + surrogateDiagTailX0RatChunk001Sub001Block070Part013
    + surrogateDiagTailX0RatChunk001Sub001Block070Part014
    + surrogateDiagTailX0RatChunk001Sub001Block070Part015
    + surrogateDiagTailX0RatChunk001Sub001Block070Part016
    + surrogateDiagTailX0RatChunk001Sub001Block070Part017
    + surrogateDiagTailX0RatChunk001Sub001Block070Part018
    + surrogateDiagTailX0RatChunk001Sub001Block070Part019

def surrogateDiagonalTailChunk001Sub001Block070TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block070Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block070Part020
    + surrogateDiagTailX0RatChunk001Sub001Block070Part021
    + surrogateDiagTailX0RatChunk001Sub001Block070Part022
    + surrogateDiagTailX0RatChunk001Sub001Block070Part023
    + surrogateDiagTailX0RatChunk001Sub001Block070Part024

def surrogateDiagonalTailChunk001Sub001Block070Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block070HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block070MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block070TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block070 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block070Part000
    + surrogateDiagTailX0RatChunk001Sub001Block070Part001
    + surrogateDiagTailX0RatChunk001Sub001Block070Part002
    + surrogateDiagTailX0RatChunk001Sub001Block070Part003
    + surrogateDiagTailX0RatChunk001Sub001Block070Part004
    + surrogateDiagTailX0RatChunk001Sub001Block070Part005
    + surrogateDiagTailX0RatChunk001Sub001Block070Part006
    + surrogateDiagTailX0RatChunk001Sub001Block070Part007
    + surrogateDiagTailX0RatChunk001Sub001Block070Part008
    + surrogateDiagTailX0RatChunk001Sub001Block070Part009
    + surrogateDiagTailX0RatChunk001Sub001Block070Part010
    + surrogateDiagTailX0RatChunk001Sub001Block070Part011
    + surrogateDiagTailX0RatChunk001Sub001Block070Part012
    + surrogateDiagTailX0RatChunk001Sub001Block070Part013
    + surrogateDiagTailX0RatChunk001Sub001Block070Part014
    + surrogateDiagTailX0RatChunk001Sub001Block070Part015
    + surrogateDiagTailX0RatChunk001Sub001Block070Part016
    + surrogateDiagTailX0RatChunk001Sub001Block070Part017
    + surrogateDiagTailX0RatChunk001Sub001Block070Part018
    + surrogateDiagTailX0RatChunk001Sub001Block070Part019
    + surrogateDiagTailX0RatChunk001Sub001Block070Part020
    + surrogateDiagTailX0RatChunk001Sub001Block070Part021
    + surrogateDiagTailX0RatChunk001Sub001Block070Part022
    + surrogateDiagTailX0RatChunk001Sub001Block070Part023
    + surrogateDiagTailX0RatChunk001Sub001Block070Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block070_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block070Head + surrogateDiagTailX0RatChunk001Sub001Block070Mid + surrogateDiagTailX0RatChunk001Sub001Block070Tail =
      surrogateDiagTailX0RatChunk001Sub001Block070 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block070Head surrogateDiagTailX0RatChunk001Sub001Block070Mid surrogateDiagTailX0RatChunk001Sub001Block070Tail surrogateDiagTailX0RatChunk001Sub001Block070
  ring

def SurrogateDiagonalTailChunk001Sub001Block070HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block070HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block070Head

def SurrogateDiagonalTailChunk001Sub001Block070MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block070MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block070Mid

def SurrogateDiagonalTailChunk001Sub001Block070TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block070TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block070Tail

theorem surrogateDiagonalTailChunk001Sub001Block070_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block070HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block070MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block070TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block070Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block070 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block070HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block070MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block070TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block070Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block070_eq_head_add_mid_add_tail

/-- Block 071 covers tail-support indices [16775,16800) and q from 27638 to 27677. -/

def TailChunk001Sub001Block071Part000SupportExplicit : Finset ℕ :=
  ([27638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part000 : ℚ :=
  (39546892375 : ℚ) / 7328370209781123072

def SurrogateDiagonalTailChunk001Sub001Block071Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27638
    = surrogateDiagTailX0RatChunk001Sub001Block071Part000

theorem surrogateDiagonalTailChunk001Sub001Block071Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part000] using hcert

def TailChunk001Sub001Block071Part001SupportExplicit : Finset ℕ :=
  ([27641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part001 : ℚ :=
  (4251994429 : ℚ) / 55556827553682000000

def SurrogateDiagonalTailChunk001Sub001Block071Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27641
    = surrogateDiagTailX0RatChunk001Sub001Block071Part001

theorem surrogateDiagonalTailChunk001Sub001Block071Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part001] using hcert

def TailChunk001Sub001Block071Part002SupportExplicit : Finset ℕ :=
  ([27642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part002 : ℚ :=
  (53433952051 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub001Block071Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27642
    = surrogateDiagTailX0RatChunk001Sub001Block071Part002

theorem surrogateDiagonalTailChunk001Sub001Block071Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part002] using hcert

def TailChunk001Sub001Block071Part003SupportExplicit : Finset ℕ :=
  ([27643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part003 : ℚ :=
  (59389292893 : ℚ) / 21292367743240243200

def SurrogateDiagonalTailChunk001Sub001Block071Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27643
    = surrogateDiagTailX0RatChunk001Sub001Block071Part003

theorem surrogateDiagonalTailChunk001Sub001Block071Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part003] using hcert

def TailChunk001Sub001Block071Part004SupportExplicit : Finset ℕ :=
  ([27645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part004 : ℚ :=
  (709398173525 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk001Sub001Block071Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27645
    = surrogateDiagTailX0RatChunk001Sub001Block071Part004

theorem surrogateDiagonalTailChunk001Sub001Block071Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part004] using hcert

def TailChunk001Sub001Block071Part005SupportExplicit : Finset ℕ :=
  ([27646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part005 : ℚ :=
  (8361607801 : ℚ) / 3036564951552000000

def SurrogateDiagonalTailChunk001Sub001Block071Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27646
    = surrogateDiagTailX0RatChunk001Sub001Block071Part005

theorem surrogateDiagonalTailChunk001Sub001Block071Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part005] using hcert

def TailChunk001Sub001Block071Part006SupportExplicit : Finset ℕ :=
  ([27647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block071Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27647
    = surrogateDiagTailX0RatChunk001Sub001Block071Part006

theorem surrogateDiagonalTailChunk001Sub001Block071Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part006] using hcert

def TailChunk001Sub001Block071Part007SupportExplicit : Finset ℕ :=
  ([27649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part007 : ℚ :=
  (109497614375 : ℚ) / 660897542661456227904

def SurrogateDiagonalTailChunk001Sub001Block071Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27649
    = surrogateDiagTailX0RatChunk001Sub001Block071Part007

theorem surrogateDiagonalTailChunk001Sub001Block071Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part007] using hcert

def TailChunk001Sub001Block071Part008SupportExplicit : Finset ℕ :=
  ([27651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part008 : ℚ :=
  (12964084025 : ℚ) / 6514106853138776064

def SurrogateDiagonalTailChunk001Sub001Block071Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27651
    = surrogateDiagTailX0RatChunk001Sub001Block071Part008

theorem surrogateDiagonalTailChunk001Sub001Block071Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part008] using hcert

def TailChunk001Sub001Block071Part009SupportExplicit : Finset ℕ :=
  ([27653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block071Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27653
    = surrogateDiagTailX0RatChunk001Sub001Block071Part009

theorem surrogateDiagonalTailChunk001Sub001Block071Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part009] using hcert

def TailChunk001Sub001Block071Part010SupportExplicit : Finset ℕ :=
  ([27654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part010 : ℚ :=
  (112454007 : ℚ) / 1017819395707840

def SurrogateDiagonalTailChunk001Sub001Block071Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27654
    = surrogateDiagTailX0RatChunk001Sub001Block071Part010

theorem surrogateDiagonalTailChunk001Sub001Block071Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part010] using hcert

def TailChunk001Sub001Block071Part011SupportExplicit : Finset ℕ :=
  ([27655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part011 : ℚ :=
  (5100151323 : ℚ) / 1596379277822228480

def SurrogateDiagonalTailChunk001Sub001Block071Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27655
    = surrogateDiagTailX0RatChunk001Sub001Block071Part011

theorem surrogateDiagonalTailChunk001Sub001Block071Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part011] using hcert

def TailChunk001Sub001Block071Part012SupportExplicit : Finset ℕ :=
  ([27658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block071Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27658
    = surrogateDiagTailX0RatChunk001Sub001Block071Part012

theorem surrogateDiagonalTailChunk001Sub001Block071Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part012] using hcert

def TailChunk001Sub001Block071Part013SupportExplicit : Finset ℕ :=
  ([27659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part013 : ℚ :=
  (13903540525 : ℚ) / 31818994662680690688

def SurrogateDiagonalTailChunk001Sub001Block071Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27659
    = surrogateDiagTailX0RatChunk001Sub001Block071Part013

theorem surrogateDiagonalTailChunk001Sub001Block071Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part013] using hcert

def TailChunk001Sub001Block071Part014SupportExplicit : Finset ℕ :=
  ([27661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part014 : ℚ :=
  (52062563375 : ℚ) / 696905624959531758144

def SurrogateDiagonalTailChunk001Sub001Block071Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27661
    = surrogateDiagTailX0RatChunk001Sub001Block071Part014

theorem surrogateDiagonalTailChunk001Sub001Block071Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part014] using hcert

def TailChunk001Sub001Block071Part015SupportExplicit : Finset ℕ :=
  ([27662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block071Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27662
    = surrogateDiagTailX0RatChunk001Sub001Block071Part015

theorem surrogateDiagonalTailChunk001Sub001Block071Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part015] using hcert

def TailChunk001Sub001Block071Part016SupportExplicit : Finset ℕ :=
  ([27663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part016 : ℚ :=
  (5001 : ℚ) / 2312456982579200

def SurrogateDiagonalTailChunk001Sub001Block071Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27663
    = surrogateDiagTailX0RatChunk001Sub001Block071Part016

theorem surrogateDiagonalTailChunk001Sub001Block071Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part016] using hcert

def TailChunk001Sub001Block071Part017SupportExplicit : Finset ℕ :=
  ([27665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part017 : ℚ :=
  (87440820793 : ℚ) / 16260791608116019200

def SurrogateDiagonalTailChunk001Sub001Block071Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27665
    = surrogateDiagTailX0RatChunk001Sub001Block071Part017

theorem surrogateDiagonalTailChunk001Sub001Block071Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part017] using hcert

def TailChunk001Sub001Block071Part018SupportExplicit : Finset ℕ :=
  ([27667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part018 : ℚ :=
  (1279273475 : ℚ) / 12702824221461405696

def SurrogateDiagonalTailChunk001Sub001Block071Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27667
    = surrogateDiagTailX0RatChunk001Sub001Block071Part018

theorem surrogateDiagonalTailChunk001Sub001Block071Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part018] using hcert

def TailChunk001Sub001Block071Part019SupportExplicit : Finset ℕ :=
  ([27669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part019 : ℚ :=
  (1054980967 : ℚ) / 959704478515200000

def SurrogateDiagonalTailChunk001Sub001Block071Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27669
    = surrogateDiagTailX0RatChunk001Sub001Block071Part019

theorem surrogateDiagonalTailChunk001Sub001Block071Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part019] using hcert

def TailChunk001Sub001Block071Part020SupportExplicit : Finset ℕ :=
  ([27670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part020 : ℚ :=
  (319134508675 : ℚ) / 12489765159468865536

def SurrogateDiagonalTailChunk001Sub001Block071Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27670
    = surrogateDiagTailX0RatChunk001Sub001Block071Part020

theorem surrogateDiagonalTailChunk001Sub001Block071Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part020] using hcert

def TailChunk001Sub001Block071Part021SupportExplicit : Finset ℕ :=
  ([27671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part021 : ℚ :=
  (1139134590025 : ℚ) / 695856321341562636288

def SurrogateDiagonalTailChunk001Sub001Block071Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27671
    = surrogateDiagTailX0RatChunk001Sub001Block071Part021

theorem surrogateDiagonalTailChunk001Sub001Block071Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part021] using hcert

def TailChunk001Sub001Block071Part022SupportExplicit : Finset ℕ :=
  ([27673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block071Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27673
    = surrogateDiagTailX0RatChunk001Sub001Block071Part022

theorem surrogateDiagonalTailChunk001Sub001Block071Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part022] using hcert

def TailChunk001Sub001Block071Part023SupportExplicit : Finset ℕ :=
  ([27674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part023 : ℚ :=
  (986887557 : ℚ) / 1140568121344000000

def SurrogateDiagonalTailChunk001Sub001Block071Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27674
    = surrogateDiagTailX0RatChunk001Sub001Block071Part023

theorem surrogateDiagonalTailChunk001Sub001Block071Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part023] using hcert

def TailChunk001Sub001Block071Part024SupportExplicit : Finset ℕ :=
  ([27677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block071Part024 : ℚ :=
  (60891808325 : ℚ) / 75946943780877238272

def SurrogateDiagonalTailChunk001Sub001Block071Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27677
    = surrogateDiagTailX0RatChunk001Sub001Block071Part024

theorem surrogateDiagonalTailChunk001Sub001Block071Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block071Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block071Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block071Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block071Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block071Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block071HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block071Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block071Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block071Part000
    + surrogateDiagTailX0RatChunk001Sub001Block071Part001
    + surrogateDiagTailX0RatChunk001Sub001Block071Part002
    + surrogateDiagTailX0RatChunk001Sub001Block071Part003
    + surrogateDiagTailX0RatChunk001Sub001Block071Part004
    + surrogateDiagTailX0RatChunk001Sub001Block071Part005
    + surrogateDiagTailX0RatChunk001Sub001Block071Part006
    + surrogateDiagTailX0RatChunk001Sub001Block071Part007
    + surrogateDiagTailX0RatChunk001Sub001Block071Part008
    + surrogateDiagTailX0RatChunk001Sub001Block071Part009

def surrogateDiagonalTailChunk001Sub001Block071MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block071Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block071Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block071Part010
    + surrogateDiagTailX0RatChunk001Sub001Block071Part011
    + surrogateDiagTailX0RatChunk001Sub001Block071Part012
    + surrogateDiagTailX0RatChunk001Sub001Block071Part013
    + surrogateDiagTailX0RatChunk001Sub001Block071Part014
    + surrogateDiagTailX0RatChunk001Sub001Block071Part015
    + surrogateDiagTailX0RatChunk001Sub001Block071Part016
    + surrogateDiagTailX0RatChunk001Sub001Block071Part017
    + surrogateDiagTailX0RatChunk001Sub001Block071Part018
    + surrogateDiagTailX0RatChunk001Sub001Block071Part019

def surrogateDiagonalTailChunk001Sub001Block071TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block071Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block071Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block071Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block071Part020
    + surrogateDiagTailX0RatChunk001Sub001Block071Part021
    + surrogateDiagTailX0RatChunk001Sub001Block071Part022
    + surrogateDiagTailX0RatChunk001Sub001Block071Part023
    + surrogateDiagTailX0RatChunk001Sub001Block071Part024

def surrogateDiagonalTailChunk001Sub001Block071Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block071HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block071MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block071TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block071 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block071Part000
    + surrogateDiagTailX0RatChunk001Sub001Block071Part001
    + surrogateDiagTailX0RatChunk001Sub001Block071Part002
    + surrogateDiagTailX0RatChunk001Sub001Block071Part003
    + surrogateDiagTailX0RatChunk001Sub001Block071Part004
    + surrogateDiagTailX0RatChunk001Sub001Block071Part005
    + surrogateDiagTailX0RatChunk001Sub001Block071Part006
    + surrogateDiagTailX0RatChunk001Sub001Block071Part007
    + surrogateDiagTailX0RatChunk001Sub001Block071Part008
    + surrogateDiagTailX0RatChunk001Sub001Block071Part009
    + surrogateDiagTailX0RatChunk001Sub001Block071Part010
    + surrogateDiagTailX0RatChunk001Sub001Block071Part011
    + surrogateDiagTailX0RatChunk001Sub001Block071Part012
    + surrogateDiagTailX0RatChunk001Sub001Block071Part013
    + surrogateDiagTailX0RatChunk001Sub001Block071Part014
    + surrogateDiagTailX0RatChunk001Sub001Block071Part015
    + surrogateDiagTailX0RatChunk001Sub001Block071Part016
    + surrogateDiagTailX0RatChunk001Sub001Block071Part017
    + surrogateDiagTailX0RatChunk001Sub001Block071Part018
    + surrogateDiagTailX0RatChunk001Sub001Block071Part019
    + surrogateDiagTailX0RatChunk001Sub001Block071Part020
    + surrogateDiagTailX0RatChunk001Sub001Block071Part021
    + surrogateDiagTailX0RatChunk001Sub001Block071Part022
    + surrogateDiagTailX0RatChunk001Sub001Block071Part023
    + surrogateDiagTailX0RatChunk001Sub001Block071Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block071_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block071Head + surrogateDiagTailX0RatChunk001Sub001Block071Mid + surrogateDiagTailX0RatChunk001Sub001Block071Tail =
      surrogateDiagTailX0RatChunk001Sub001Block071 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block071Head surrogateDiagTailX0RatChunk001Sub001Block071Mid surrogateDiagTailX0RatChunk001Sub001Block071Tail surrogateDiagTailX0RatChunk001Sub001Block071
  ring

def SurrogateDiagonalTailChunk001Sub001Block071HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block071HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block071Head

def SurrogateDiagonalTailChunk001Sub001Block071MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block071MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block071Mid

def SurrogateDiagonalTailChunk001Sub001Block071TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block071TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block071Tail

theorem surrogateDiagonalTailChunk001Sub001Block071_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block071HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block071MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block071TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block071Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block071 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block071HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block071MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block071TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block071Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block071_eq_head_add_mid_add_tail

/-- Block 072 covers tail-support indices [16800,16825) and q from 27678 to 27717. -/

def TailChunk001Sub001Block072Part000SupportExplicit : Finset ℕ :=
  ([27678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part000 : ℚ :=
  (1410813375925 : ℚ) / 9719757226077308928

def SurrogateDiagonalTailChunk001Sub001Block072Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27678
    = surrogateDiagTailX0RatChunk001Sub001Block072Part000

theorem surrogateDiagonalTailChunk001Sub001Block072Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part000] using hcert

def TailChunk001Sub001Block072Part001SupportExplicit : Finset ℕ :=
  ([27679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part001 : ℚ :=
  (77313919 : ℚ) / 865534413772300800

def SurrogateDiagonalTailChunk001Sub001Block072Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27679
    = surrogateDiagTailX0RatChunk001Sub001Block072Part001

theorem surrogateDiagonalTailChunk001Sub001Block072Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part001] using hcert

def TailChunk001Sub001Block072Part002SupportExplicit : Finset ℕ :=
  ([27681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part002 : ℚ :=
  (125025 : ℚ) / 57962056792750208

def SurrogateDiagonalTailChunk001Sub001Block072Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27681
    = surrogateDiagTailX0RatChunk001Sub001Block072Part002

theorem surrogateDiagonalTailChunk001Sub001Block072Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part002] using hcert

def TailChunk001Sub001Block072Part003SupportExplicit : Finset ℕ :=
  ([27682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block072Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27682
    = surrogateDiagTailX0RatChunk001Sub001Block072Part003

theorem surrogateDiagonalTailChunk001Sub001Block072Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part003] using hcert

def TailChunk001Sub001Block072Part004SupportExplicit : Finset ℕ :=
  ([27683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part004 : ℚ :=
  (1340911387 : ℚ) / 1586653063223212800

def SurrogateDiagonalTailChunk001Sub001Block072Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27683
    = surrogateDiagTailX0RatChunk001Sub001Block072Part004

theorem surrogateDiagonalTailChunk001Sub001Block072Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part004] using hcert

def TailChunk001Sub001Block072Part005SupportExplicit : Finset ℕ :=
  ([27686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part005 : ℚ :=
  (5160374525 : ℚ) / 6124575963918892032

def SurrogateDiagonalTailChunk001Sub001Block072Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27686
    = surrogateDiagTailX0RatChunk001Sub001Block072Part005

theorem surrogateDiagonalTailChunk001Sub001Block072Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part005] using hcert

def TailChunk001Sub001Block072Part006SupportExplicit : Finset ℕ :=
  ([27687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part006 : ℚ :=
  (21322030993 : ℚ) / 7891924237809715200

def SurrogateDiagonalTailChunk001Sub001Block072Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27687
    = surrogateDiagTailX0RatChunk001Sub001Block072Part006

theorem surrogateDiagonalTailChunk001Sub001Block072Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part006] using hcert

def TailChunk001Sub001Block072Part007SupportExplicit : Finset ℕ :=
  ([27689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block072Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27689
    = surrogateDiagTailX0RatChunk001Sub001Block072Part007

theorem surrogateDiagonalTailChunk001Sub001Block072Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part007] using hcert

def TailChunk001Sub001Block072Part008SupportExplicit : Finset ℕ :=
  ([27690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part008 : ℚ :=
  (7929516337 : ℚ) / 29138413525401600

def SurrogateDiagonalTailChunk001Sub001Block072Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27690
    = surrogateDiagTailX0RatChunk001Sub001Block072Part008

theorem surrogateDiagonalTailChunk001Sub001Block072Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part008] using hcert

def TailChunk001Sub001Block072Part009SupportExplicit : Finset ℕ :=
  ([27691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block072Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27691
    = surrogateDiagTailX0RatChunk001Sub001Block072Part009

theorem surrogateDiagonalTailChunk001Sub001Block072Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part009] using hcert

def TailChunk001Sub001Block072Part010SupportExplicit : Finset ℕ :=
  ([27694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part010 : ℚ :=
  (295638281 : ℚ) / 281802188975961600

def SurrogateDiagonalTailChunk001Sub001Block072Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27694
    = surrogateDiagTailX0RatChunk001Sub001Block072Part010

theorem surrogateDiagonalTailChunk001Sub001Block072Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part010] using hcert

def TailChunk001Sub001Block072Part011SupportExplicit : Finset ℕ :=
  ([27695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part011 : ℚ :=
  (27055368957 : ℚ) / 6836787634595430400

def SurrogateDiagonalTailChunk001Sub001Block072Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27695
    = surrogateDiagTailX0RatChunk001Sub001Block072Part011

theorem surrogateDiagonalTailChunk001Sub001Block072Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part011] using hcert

def TailChunk001Sub001Block072Part012SupportExplicit : Finset ℕ :=
  ([27697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block072Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27697
    = surrogateDiagTailX0RatChunk001Sub001Block072Part012

theorem surrogateDiagonalTailChunk001Sub001Block072Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part012] using hcert

def TailChunk001Sub001Block072Part013SupportExplicit : Finset ℕ :=
  ([27698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part013 : ℚ :=
  (5313744783 : ℚ) / 835003238619606400

def SurrogateDiagonalTailChunk001Sub001Block072Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27698
    = surrogateDiagTailX0RatChunk001Sub001Block072Part013

theorem surrogateDiagonalTailChunk001Sub001Block072Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part013] using hcert

def TailChunk001Sub001Block072Part014SupportExplicit : Finset ℕ :=
  ([27699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part014 : ℚ :=
  (2729875 : ℚ) / 651801554937216

def SurrogateDiagonalTailChunk001Sub001Block072Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27699
    = surrogateDiagTailX0RatChunk001Sub001Block072Part014

theorem surrogateDiagonalTailChunk001Sub001Block072Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part014] using hcert

def TailChunk001Sub001Block072Part015SupportExplicit : Finset ℕ :=
  ([27701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block072Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27701
    = surrogateDiagTailX0RatChunk001Sub001Block072Part015

theorem surrogateDiagonalTailChunk001Sub001Block072Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part015] using hcert

def TailChunk001Sub001Block072Part016SupportExplicit : Finset ℕ :=
  ([27703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part016 : ℚ :=
  (2536678061 : ℚ) / 4743378040854988800

def SurrogateDiagonalTailChunk001Sub001Block072Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27703
    = surrogateDiagTailX0RatChunk001Sub001Block072Part016

theorem surrogateDiagonalTailChunk001Sub001Block072Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part016] using hcert

def TailChunk001Sub001Block072Part017SupportExplicit : Finset ℕ :=
  ([27705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part017 : ℚ :=
  (160081165925 : ℚ) / 14867009078173863936

def SurrogateDiagonalTailChunk001Sub001Block072Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27705
    = surrogateDiagTailX0RatChunk001Sub001Block072Part017

theorem surrogateDiagonalTailChunk001Sub001Block072Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part017] using hcert

def TailChunk001Sub001Block072Part018SupportExplicit : Finset ℕ :=
  ([27706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part018 : ℚ :=
  (40842885475 : ℚ) / 2755906660163889216

def SurrogateDiagonalTailChunk001Sub001Block072Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27706
    = surrogateDiagTailX0RatChunk001Sub001Block072Part018

theorem surrogateDiagonalTailChunk001Sub001Block072Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part018] using hcert

def TailChunk001Sub001Block072Part019SupportExplicit : Finset ℕ :=
  ([27707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part019 : ℚ :=
  (116515450825 : ℚ) / 1396261367983196817408

def SurrogateDiagonalTailChunk001Sub001Block072Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27707
    = surrogateDiagTailX0RatChunk001Sub001Block072Part019

theorem surrogateDiagonalTailChunk001Sub001Block072Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part019] using hcert

def TailChunk001Sub001Block072Part020SupportExplicit : Finset ℕ :=
  ([27710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part020 : ℚ :=
  (1054847204125 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub001Block072Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27710
    = surrogateDiagTailX0RatChunk001Sub001Block072Part020

theorem surrogateDiagonalTailChunk001Sub001Block072Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part020] using hcert

def TailChunk001Sub001Block072Part021SupportExplicit : Finset ℕ :=
  ([27713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part021 : ℚ :=
  (590510934575 : ℚ) / 343585896705525694464

def SurrogateDiagonalTailChunk001Sub001Block072Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27713
    = surrogateDiagTailX0RatChunk001Sub001Block072Part021

theorem surrogateDiagonalTailChunk001Sub001Block072Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part021] using hcert

def TailChunk001Sub001Block072Part022SupportExplicit : Finset ℕ :=
  ([27714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part022 : ℚ :=
  (26823646169 : ℚ) / 310963000131993600

def SurrogateDiagonalTailChunk001Sub001Block072Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27714
    = surrogateDiagTailX0RatChunk001Sub001Block072Part022

theorem surrogateDiagonalTailChunk001Sub001Block072Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part022] using hcert

def TailChunk001Sub001Block072Part023SupportExplicit : Finset ℕ :=
  ([27715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part023 : ℚ :=
  (42239435561 : ℚ) / 9950216033245593600

def SurrogateDiagonalTailChunk001Sub001Block072Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27715
    = surrogateDiagTailX0RatChunk001Sub001Block072Part023

theorem surrogateDiagonalTailChunk001Sub001Block072Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part023] using hcert

def TailChunk001Sub001Block072Part024SupportExplicit : Finset ℕ :=
  ([27717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block072Part024 : ℚ :=
  (125025 : ℚ) / 58264204146677888

def SurrogateDiagonalTailChunk001Sub001Block072Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27717
    = surrogateDiagTailX0RatChunk001Sub001Block072Part024

theorem surrogateDiagonalTailChunk001Sub001Block072Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block072Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block072Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block072Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block072Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block072Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block072HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block072Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block072Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block072Part000
    + surrogateDiagTailX0RatChunk001Sub001Block072Part001
    + surrogateDiagTailX0RatChunk001Sub001Block072Part002
    + surrogateDiagTailX0RatChunk001Sub001Block072Part003
    + surrogateDiagTailX0RatChunk001Sub001Block072Part004
    + surrogateDiagTailX0RatChunk001Sub001Block072Part005
    + surrogateDiagTailX0RatChunk001Sub001Block072Part006
    + surrogateDiagTailX0RatChunk001Sub001Block072Part007
    + surrogateDiagTailX0RatChunk001Sub001Block072Part008
    + surrogateDiagTailX0RatChunk001Sub001Block072Part009

def surrogateDiagonalTailChunk001Sub001Block072MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block072Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block072Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block072Part010
    + surrogateDiagTailX0RatChunk001Sub001Block072Part011
    + surrogateDiagTailX0RatChunk001Sub001Block072Part012
    + surrogateDiagTailX0RatChunk001Sub001Block072Part013
    + surrogateDiagTailX0RatChunk001Sub001Block072Part014
    + surrogateDiagTailX0RatChunk001Sub001Block072Part015
    + surrogateDiagTailX0RatChunk001Sub001Block072Part016
    + surrogateDiagTailX0RatChunk001Sub001Block072Part017
    + surrogateDiagTailX0RatChunk001Sub001Block072Part018
    + surrogateDiagTailX0RatChunk001Sub001Block072Part019

def surrogateDiagonalTailChunk001Sub001Block072TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block072Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block072Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block072Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block072Part020
    + surrogateDiagTailX0RatChunk001Sub001Block072Part021
    + surrogateDiagTailX0RatChunk001Sub001Block072Part022
    + surrogateDiagTailX0RatChunk001Sub001Block072Part023
    + surrogateDiagTailX0RatChunk001Sub001Block072Part024

def surrogateDiagonalTailChunk001Sub001Block072Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block072HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block072MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block072TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block072 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block072Part000
    + surrogateDiagTailX0RatChunk001Sub001Block072Part001
    + surrogateDiagTailX0RatChunk001Sub001Block072Part002
    + surrogateDiagTailX0RatChunk001Sub001Block072Part003
    + surrogateDiagTailX0RatChunk001Sub001Block072Part004
    + surrogateDiagTailX0RatChunk001Sub001Block072Part005
    + surrogateDiagTailX0RatChunk001Sub001Block072Part006
    + surrogateDiagTailX0RatChunk001Sub001Block072Part007
    + surrogateDiagTailX0RatChunk001Sub001Block072Part008
    + surrogateDiagTailX0RatChunk001Sub001Block072Part009
    + surrogateDiagTailX0RatChunk001Sub001Block072Part010
    + surrogateDiagTailX0RatChunk001Sub001Block072Part011
    + surrogateDiagTailX0RatChunk001Sub001Block072Part012
    + surrogateDiagTailX0RatChunk001Sub001Block072Part013
    + surrogateDiagTailX0RatChunk001Sub001Block072Part014
    + surrogateDiagTailX0RatChunk001Sub001Block072Part015
    + surrogateDiagTailX0RatChunk001Sub001Block072Part016
    + surrogateDiagTailX0RatChunk001Sub001Block072Part017
    + surrogateDiagTailX0RatChunk001Sub001Block072Part018
    + surrogateDiagTailX0RatChunk001Sub001Block072Part019
    + surrogateDiagTailX0RatChunk001Sub001Block072Part020
    + surrogateDiagTailX0RatChunk001Sub001Block072Part021
    + surrogateDiagTailX0RatChunk001Sub001Block072Part022
    + surrogateDiagTailX0RatChunk001Sub001Block072Part023
    + surrogateDiagTailX0RatChunk001Sub001Block072Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block072_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block072Head + surrogateDiagTailX0RatChunk001Sub001Block072Mid + surrogateDiagTailX0RatChunk001Sub001Block072Tail =
      surrogateDiagTailX0RatChunk001Sub001Block072 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block072Head surrogateDiagTailX0RatChunk001Sub001Block072Mid surrogateDiagTailX0RatChunk001Sub001Block072Tail surrogateDiagTailX0RatChunk001Sub001Block072
  ring

def SurrogateDiagonalTailChunk001Sub001Block072HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block072HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block072Head

def SurrogateDiagonalTailChunk001Sub001Block072MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block072MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block072Mid

def SurrogateDiagonalTailChunk001Sub001Block072TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block072TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block072Tail

theorem surrogateDiagonalTailChunk001Sub001Block072_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block072HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block072MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block072TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block072Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block072 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block072HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block072MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block072TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block072Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block072_eq_head_add_mid_add_tail

/-- Block 073 covers tail-support indices [16825,16850) and q from 27718 to 27761. -/

def TailChunk001Sub001Block073Part000SupportExplicit : Finset ℕ :=
  ([27718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27718
    = surrogateDiagTailX0RatChunk001Sub001Block073Part000

theorem surrogateDiagonalTailChunk001Sub001Block073Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part000] using hcert

def TailChunk001Sub001Block073Part001SupportExplicit : Finset ℕ :=
  ([27719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part001 : ℚ :=
  (84693137825 : ℚ) / 678722505082862183424

def SurrogateDiagonalTailChunk001Sub001Block073Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27719
    = surrogateDiagTailX0RatChunk001Sub001Block073Part001

theorem surrogateDiagonalTailChunk001Sub001Block073Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part001] using hcert

def TailChunk001Sub001Block073Part002SupportExplicit : Finset ℕ :=
  ([27721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part002 : ℚ :=
  (19879440175 : ℚ) / 43932226201827825024

def SurrogateDiagonalTailChunk001Sub001Block073Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27721
    = surrogateDiagTailX0RatChunk001Sub001Block073Part002

theorem surrogateDiagonalTailChunk001Sub001Block073Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part002] using hcert

def TailChunk001Sub001Block073Part003SupportExplicit : Finset ℕ :=
  ([27722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part003 : ℚ :=
  (9398962175 : ℚ) / 10730615502544196496

def SurrogateDiagonalTailChunk001Sub001Block073Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27722
    = surrogateDiagTailX0RatChunk001Sub001Block073Part003

theorem surrogateDiagonalTailChunk001Sub001Block073Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part003] using hcert

def TailChunk001Sub001Block073Part004SupportExplicit : Finset ℕ :=
  ([27723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part004 : ℚ :=
  (1667 : ℚ) / 777529022054400

def SurrogateDiagonalTailChunk001Sub001Block073Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27723
    = surrogateDiagTailX0RatChunk001Sub001Block073Part004

theorem surrogateDiagonalTailChunk001Sub001Block073Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part004] using hcert

def TailChunk001Sub001Block073Part005SupportExplicit : Finset ℕ :=
  ([27726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part005 : ℚ :=
  (23833037 : ℚ) / 325481805744480

def SurrogateDiagonalTailChunk001Sub001Block073Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27726
    = surrogateDiagTailX0RatChunk001Sub001Block073Part005

theorem surrogateDiagonalTailChunk001Sub001Block073Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part005] using hcert

def TailChunk001Sub001Block073Part006SupportExplicit : Finset ℕ :=
  ([27727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part006 : ℚ :=
  (22674160525 : ℚ) / 10608054371579068416

def SurrogateDiagonalTailChunk001Sub001Block073Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27727
    = surrogateDiagTailX0RatChunk001Sub001Block073Part006

theorem surrogateDiagonalTailChunk001Sub001Block073Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part006] using hcert

def TailChunk001Sub001Block073Part007SupportExplicit : Finset ℕ :=
  ([27730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part007 : ℚ :=
  (508642433225 : ℚ) / 16217358955762827264

def SurrogateDiagonalTailChunk001Sub001Block073Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27730
    = surrogateDiagTailX0RatChunk001Sub001Block073Part007

theorem surrogateDiagonalTailChunk001Sub001Block073Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part007] using hcert

def TailChunk001Sub001Block073Part008SupportExplicit : Finset ℕ :=
  ([27731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part008 : ℚ :=
  (2655896197 : ℚ) / 3361303806336000000

def SurrogateDiagonalTailChunk001Sub001Block073Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27731
    = surrogateDiagTailX0RatChunk001Sub001Block073Part008

theorem surrogateDiagonalTailChunk001Sub001Block073Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part008] using hcert

def TailChunk001Sub001Block073Part009SupportExplicit : Finset ℕ :=
  ([27733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27733
    = surrogateDiagTailX0RatChunk001Sub001Block073Part009

theorem surrogateDiagonalTailChunk001Sub001Block073Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part009] using hcert

def TailChunk001Sub001Block073Part010SupportExplicit : Finset ℕ :=
  ([27737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27737
    = surrogateDiagTailX0RatChunk001Sub001Block073Part010

theorem surrogateDiagonalTailChunk001Sub001Block073Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part010] using hcert

def TailChunk001Sub001Block073Part011SupportExplicit : Finset ℕ :=
  ([27739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27739
    = surrogateDiagTailX0RatChunk001Sub001Block073Part011

theorem surrogateDiagonalTailChunk001Sub001Block073Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part011] using hcert

def TailChunk001Sub001Block073Part012SupportExplicit : Finset ℕ :=
  ([27741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part012 : ℚ :=
  (30647193367 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk001Sub001Block073Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27741
    = surrogateDiagTailX0RatChunk001Sub001Block073Part012

theorem surrogateDiagonalTailChunk001Sub001Block073Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part012] using hcert

def TailChunk001Sub001Block073Part013SupportExplicit : Finset ℕ :=
  ([27742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part013 : ℚ :=
  (909056627 : ℚ) / 58718575594045440

def SurrogateDiagonalTailChunk001Sub001Block073Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27742
    = surrogateDiagTailX0RatChunk001Sub001Block073Part013

theorem surrogateDiagonalTailChunk001Sub001Block073Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part013] using hcert

def TailChunk001Sub001Block073Part014SupportExplicit : Finset ℕ :=
  ([27743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27743
    = surrogateDiagTailX0RatChunk001Sub001Block073Part014

theorem surrogateDiagonalTailChunk001Sub001Block073Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part014] using hcert

def TailChunk001Sub001Block073Part015SupportExplicit : Finset ℕ :=
  ([27745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part015 : ℚ :=
  (27358893607 : ℚ) / 6940177674655334400

def SurrogateDiagonalTailChunk001Sub001Block073Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27745
    = surrogateDiagTailX0RatChunk001Sub001Block073Part015

theorem surrogateDiagonalTailChunk001Sub001Block073Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part015] using hcert

def TailChunk001Sub001Block073Part016SupportExplicit : Finset ℕ :=
  ([27746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27746
    = surrogateDiagTailX0RatChunk001Sub001Block073Part016

theorem surrogateDiagonalTailChunk001Sub001Block073Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part016] using hcert

def TailChunk001Sub001Block073Part017SupportExplicit : Finset ℕ :=
  ([27749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27749
    = surrogateDiagTailX0RatChunk001Sub001Block073Part017

theorem surrogateDiagonalTailChunk001Sub001Block073Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part017] using hcert

def TailChunk001Sub001Block073Part018SupportExplicit : Finset ℕ :=
  ([27751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27751
    = surrogateDiagTailX0RatChunk001Sub001Block073Part018

theorem surrogateDiagonalTailChunk001Sub001Block073Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part018] using hcert

def TailChunk001Sub001Block073Part019SupportExplicit : Finset ℕ :=
  ([27754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27754
    = surrogateDiagTailX0RatChunk001Sub001Block073Part019

theorem surrogateDiagonalTailChunk001Sub001Block073Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part019] using hcert

def TailChunk001Sub001Block073Part020SupportExplicit : Finset ℕ :=
  ([27755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part020 : ℚ :=
  (46754696911 : ℚ) / 8917883668345651200

def SurrogateDiagonalTailChunk001Sub001Block073Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27755
    = surrogateDiagTailX0RatChunk001Sub001Block073Part020

theorem surrogateDiagonalTailChunk001Sub001Block073Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part020] using hcert

def TailChunk001Sub001Block073Part021SupportExplicit : Finset ℕ :=
  ([27757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part021 : ℚ :=
  (707310471 : ℚ) / 4455868373096857600

def SurrogateDiagonalTailChunk001Sub001Block073Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27757
    = surrogateDiagTailX0RatChunk001Sub001Block073Part021

theorem surrogateDiagonalTailChunk001Sub001Block073Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part021] using hcert

def TailChunk001Sub001Block073Part022SupportExplicit : Finset ℕ :=
  ([27758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block073Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27758
    = surrogateDiagTailX0RatChunk001Sub001Block073Part022

theorem surrogateDiagonalTailChunk001Sub001Block073Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part022] using hcert

def TailChunk001Sub001Block073Part023SupportExplicit : Finset ℕ :=
  ([27759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part023 : ℚ :=
  (8105586425 : ℚ) / 6508477955826344448

def SurrogateDiagonalTailChunk001Sub001Block073Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27759
    = surrogateDiagTailX0RatChunk001Sub001Block073Part023

theorem surrogateDiagonalTailChunk001Sub001Block073Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part023] using hcert

def TailChunk001Sub001Block073Part024SupportExplicit : Finset ℕ :=
  ([27761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block073Part024 : ℚ :=
  (25915861 : ℚ) / 26871725398425600

def SurrogateDiagonalTailChunk001Sub001Block073Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27761
    = surrogateDiagTailX0RatChunk001Sub001Block073Part024

theorem surrogateDiagonalTailChunk001Sub001Block073Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block073Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block073Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block073Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block073Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block073Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block073HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block073Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block073Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block073Part000
    + surrogateDiagTailX0RatChunk001Sub001Block073Part001
    + surrogateDiagTailX0RatChunk001Sub001Block073Part002
    + surrogateDiagTailX0RatChunk001Sub001Block073Part003
    + surrogateDiagTailX0RatChunk001Sub001Block073Part004
    + surrogateDiagTailX0RatChunk001Sub001Block073Part005
    + surrogateDiagTailX0RatChunk001Sub001Block073Part006
    + surrogateDiagTailX0RatChunk001Sub001Block073Part007
    + surrogateDiagTailX0RatChunk001Sub001Block073Part008
    + surrogateDiagTailX0RatChunk001Sub001Block073Part009

def surrogateDiagonalTailChunk001Sub001Block073MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block073Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block073Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block073Part010
    + surrogateDiagTailX0RatChunk001Sub001Block073Part011
    + surrogateDiagTailX0RatChunk001Sub001Block073Part012
    + surrogateDiagTailX0RatChunk001Sub001Block073Part013
    + surrogateDiagTailX0RatChunk001Sub001Block073Part014
    + surrogateDiagTailX0RatChunk001Sub001Block073Part015
    + surrogateDiagTailX0RatChunk001Sub001Block073Part016
    + surrogateDiagTailX0RatChunk001Sub001Block073Part017
    + surrogateDiagTailX0RatChunk001Sub001Block073Part018
    + surrogateDiagTailX0RatChunk001Sub001Block073Part019

def surrogateDiagonalTailChunk001Sub001Block073TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block073Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block073Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block073Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block073Part020
    + surrogateDiagTailX0RatChunk001Sub001Block073Part021
    + surrogateDiagTailX0RatChunk001Sub001Block073Part022
    + surrogateDiagTailX0RatChunk001Sub001Block073Part023
    + surrogateDiagTailX0RatChunk001Sub001Block073Part024

def surrogateDiagonalTailChunk001Sub001Block073Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block073HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block073MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block073TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block073 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block073Part000
    + surrogateDiagTailX0RatChunk001Sub001Block073Part001
    + surrogateDiagTailX0RatChunk001Sub001Block073Part002
    + surrogateDiagTailX0RatChunk001Sub001Block073Part003
    + surrogateDiagTailX0RatChunk001Sub001Block073Part004
    + surrogateDiagTailX0RatChunk001Sub001Block073Part005
    + surrogateDiagTailX0RatChunk001Sub001Block073Part006
    + surrogateDiagTailX0RatChunk001Sub001Block073Part007
    + surrogateDiagTailX0RatChunk001Sub001Block073Part008
    + surrogateDiagTailX0RatChunk001Sub001Block073Part009
    + surrogateDiagTailX0RatChunk001Sub001Block073Part010
    + surrogateDiagTailX0RatChunk001Sub001Block073Part011
    + surrogateDiagTailX0RatChunk001Sub001Block073Part012
    + surrogateDiagTailX0RatChunk001Sub001Block073Part013
    + surrogateDiagTailX0RatChunk001Sub001Block073Part014
    + surrogateDiagTailX0RatChunk001Sub001Block073Part015
    + surrogateDiagTailX0RatChunk001Sub001Block073Part016
    + surrogateDiagTailX0RatChunk001Sub001Block073Part017
    + surrogateDiagTailX0RatChunk001Sub001Block073Part018
    + surrogateDiagTailX0RatChunk001Sub001Block073Part019
    + surrogateDiagTailX0RatChunk001Sub001Block073Part020
    + surrogateDiagTailX0RatChunk001Sub001Block073Part021
    + surrogateDiagTailX0RatChunk001Sub001Block073Part022
    + surrogateDiagTailX0RatChunk001Sub001Block073Part023
    + surrogateDiagTailX0RatChunk001Sub001Block073Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block073_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block073Head + surrogateDiagTailX0RatChunk001Sub001Block073Mid + surrogateDiagTailX0RatChunk001Sub001Block073Tail =
      surrogateDiagTailX0RatChunk001Sub001Block073 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block073Head surrogateDiagTailX0RatChunk001Sub001Block073Mid surrogateDiagTailX0RatChunk001Sub001Block073Tail surrogateDiagTailX0RatChunk001Sub001Block073
  ring

def SurrogateDiagonalTailChunk001Sub001Block073HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block073HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block073Head

def SurrogateDiagonalTailChunk001Sub001Block073MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block073MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block073Mid

def SurrogateDiagonalTailChunk001Sub001Block073TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block073TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block073Tail

theorem surrogateDiagonalTailChunk001Sub001Block073_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block073HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block073MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block073TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block073Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block073 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block073HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block073MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block073TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block073Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block073_eq_head_add_mid_add_tail

/-- Block 074 covers tail-support indices [16850,16875) and q from 27762 to 27802. -/

def TailChunk001Sub001Block074Part000SupportExplicit : Finset ℕ :=
  ([27762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part000 : ℚ :=
  (5824939421 : ℚ) / 43726535302348800

def SurrogateDiagonalTailChunk001Sub001Block074Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27762
    = surrogateDiagTailX0RatChunk001Sub001Block074Part000

theorem surrogateDiagonalTailChunk001Sub001Block074Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part000] using hcert

def TailChunk001Sub001Block074Part001SupportExplicit : Finset ℕ :=
  ([27763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block074Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27763
    = surrogateDiagTailX0RatChunk001Sub001Block074Part001

theorem surrogateDiagonalTailChunk001Sub001Block074Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part001] using hcert

def TailChunk001Sub001Block074Part002SupportExplicit : Finset ℕ :=
  ([27766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block074Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27766
    = surrogateDiagTailX0RatChunk001Sub001Block074Part002

theorem surrogateDiagonalTailChunk001Sub001Block074Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part002] using hcert

def TailChunk001Sub001Block074Part003SupportExplicit : Finset ℕ :=
  ([27767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block074Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27767
    = surrogateDiagTailX0RatChunk001Sub001Block074Part003

theorem surrogateDiagonalTailChunk001Sub001Block074Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part003] using hcert

def TailChunk001Sub001Block074Part004SupportExplicit : Finset ℕ :=
  ([27769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part004 : ℚ :=
  (984947198125 : ℚ) / 801756888364178713728

def SurrogateDiagonalTailChunk001Sub001Block074Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27769
    = surrogateDiagTailX0RatChunk001Sub001Block074Part004

theorem surrogateDiagonalTailChunk001Sub001Block074Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part004] using hcert

def TailChunk001Sub001Block074Part005SupportExplicit : Finset ℕ :=
  ([27770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part005 : ℚ :=
  (160962280125 : ℚ) / 12671365455506046976

def SurrogateDiagonalTailChunk001Sub001Block074Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27770
    = surrogateDiagTailX0RatChunk001Sub001Block074Part005

theorem surrogateDiagonalTailChunk001Sub001Block074Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part005] using hcert

def TailChunk001Sub001Block074Part006SupportExplicit : Finset ℕ :=
  ([27771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part006 : ℚ :=
  (125025 : ℚ) / 58719638165946368

def SurrogateDiagonalTailChunk001Sub001Block074Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27771
    = surrogateDiagTailX0RatChunk001Sub001Block074Part006

theorem surrogateDiagonalTailChunk001Sub001Block074Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part006] using hcert

def TailChunk001Sub001Block074Part007SupportExplicit : Finset ℕ :=
  ([27773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block074Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27773
    = surrogateDiagTailX0RatChunk001Sub001Block074Part007

theorem surrogateDiagonalTailChunk001Sub001Block074Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part007] using hcert

def TailChunk001Sub001Block074Part008SupportExplicit : Finset ℕ :=
  ([27777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part008 : ℚ :=
  (146191113325 : ℚ) / 264364084785369612288

def SurrogateDiagonalTailChunk001Sub001Block074Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27777
    = surrogateDiagTailX0RatChunk001Sub001Block074Part008

theorem surrogateDiagonalTailChunk001Sub001Block074Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part008] using hcert

def TailChunk001Sub001Block074Part009SupportExplicit : Finset ℕ :=
  ([27778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part009 : ℚ :=
  (4814059897025 : ℚ) / 26764798359622385664

def SurrogateDiagonalTailChunk001Sub001Block074Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27778
    = surrogateDiagTailX0RatChunk001Sub001Block074Part009

theorem surrogateDiagonalTailChunk001Sub001Block074Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part009] using hcert

def TailChunk001Sub001Block074Part010SupportExplicit : Finset ℕ :=
  ([27779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part010 : ℚ :=
  (12057388140625 : ℚ) / 372195194758831352082

def SurrogateDiagonalTailChunk001Sub001Block074Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27779
    = surrogateDiagTailX0RatChunk001Sub001Block074Part010

theorem surrogateDiagonalTailChunk001Sub001Block074Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part010] using hcert

def TailChunk001Sub001Block074Part011SupportExplicit : Finset ℕ :=
  ([27781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part011 : ℚ :=
  (4626571261625 : ℚ) / 119926270218044178432

def SurrogateDiagonalTailChunk001Sub001Block074Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27781
    = surrogateDiagTailX0RatChunk001Sub001Block074Part011

theorem surrogateDiagonalTailChunk001Sub001Block074Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part011] using hcert

def TailChunk001Sub001Block074Part012SupportExplicit : Finset ℕ :=
  ([27782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part012 : ℚ :=
  (11348536086925 : ℚ) / 80236240360964179968

def SurrogateDiagonalTailChunk001Sub001Block074Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27782
    = surrogateDiagTailX0RatChunk001Sub001Block074Part012

theorem surrogateDiagonalTailChunk001Sub001Block074Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part012] using hcert

def TailChunk001Sub001Block074Part013SupportExplicit : Finset ℕ :=
  ([27785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part013 : ℚ :=
  (643133046875 : ℚ) / 12707921841306310656

def SurrogateDiagonalTailChunk001Sub001Block074Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27785
    = surrogateDiagTailX0RatChunk001Sub001Block074Part013

theorem surrogateDiagonalTailChunk001Sub001Block074Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part013] using hcert

def TailChunk001Sub001Block074Part014SupportExplicit : Finset ℕ :=
  ([27786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part014 : ℚ :=
  (707294239 : ℚ) / 1536947328000000

def SurrogateDiagonalTailChunk001Sub001Block074Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27786
    = surrogateDiagTailX0RatChunk001Sub001Block074Part014

theorem surrogateDiagonalTailChunk001Sub001Block074Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part014] using hcert

def TailChunk001Sub001Block074Part015SupportExplicit : Finset ℕ :=
  ([27787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part015 : ℚ :=
  (3768510599 : ℚ) / 109371870000000000

def SurrogateDiagonalTailChunk001Sub001Block074Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27787
    = surrogateDiagTailX0RatChunk001Sub001Block074Part015

theorem surrogateDiagonalTailChunk001Sub001Block074Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part015] using hcert

def TailChunk001Sub001Block074Part016SupportExplicit : Finset ℕ :=
  ([27789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part016 : ℚ :=
  (5148811220725 : ℚ) / 67034321489665400832

def SurrogateDiagonalTailChunk001Sub001Block074Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27789
    = surrogateDiagTailX0RatChunk001Sub001Block074Part016

theorem surrogateDiagonalTailChunk001Sub001Block074Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part016] using hcert

def TailChunk001Sub001Block074Part017SupportExplicit : Finset ℕ :=
  ([27790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part017 : ℚ :=
  (3204044054225 : ℚ) / 10200526155331928064

def SurrogateDiagonalTailChunk001Sub001Block074Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27790
    = surrogateDiagTailX0RatChunk001Sub001Block074Part017

theorem surrogateDiagonalTailChunk001Sub001Block074Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part017] using hcert

def TailChunk001Sub001Block074Part018SupportExplicit : Finset ℕ :=
  ([27791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part018 : ℚ :=
  (19308492025 : ℚ) / 596542015659032562

def SurrogateDiagonalTailChunk001Sub001Block074Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27791
    = surrogateDiagTailX0RatChunk001Sub001Block074Part018

theorem surrogateDiagonalTailChunk001Sub001Block074Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part018] using hcert

def TailChunk001Sub001Block074Part019SupportExplicit : Finset ℕ :=
  ([27793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part019 : ℚ :=
  (12069544515625 : ℚ) / 372946101711499763712

def SurrogateDiagonalTailChunk001Sub001Block074Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27793
    = surrogateDiagTailX0RatChunk001Sub001Block074Part019

theorem surrogateDiagonalTailChunk001Sub001Block074Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part019] using hcert

def TailChunk001Sub001Block074Part020SupportExplicit : Finset ℕ :=
  ([27794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part020 : ℚ :=
  (5277856899725 : ℚ) / 33729263498824925184

def SurrogateDiagonalTailChunk001Sub001Block074Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27794
    = surrogateDiagTailX0RatChunk001Sub001Block074Part020

theorem surrogateDiagonalTailChunk001Sub001Block074Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part020] using hcert

def TailChunk001Sub001Block074Part021SupportExplicit : Finset ℕ :=
  ([27795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part021 : ℚ :=
  (12569800643425 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub001Block074Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27795
    = surrogateDiagTailX0RatChunk001Sub001Block074Part021

theorem surrogateDiagonalTailChunk001Sub001Block074Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part021] using hcert

def TailChunk001Sub001Block074Part022SupportExplicit : Finset ℕ :=
  ([27798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part022 : ℚ :=
  (50911515089 : ℚ) / 128928486512394240

def SurrogateDiagonalTailChunk001Sub001Block074Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27798
    = surrogateDiagTailX0RatChunk001Sub001Block074Part022

theorem surrogateDiagonalTailChunk001Sub001Block074Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part022] using hcert

def TailChunk001Sub001Block074Part023SupportExplicit : Finset ℕ :=
  ([27799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part023 : ℚ :=
  (12074756265625 : ℚ) / 373268266557610418802

def SurrogateDiagonalTailChunk001Sub001Block074Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27799
    = surrogateDiagTailX0RatChunk001Sub001Block074Part023

theorem surrogateDiagonalTailChunk001Sub001Block074Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part023] using hcert

def TailChunk001Sub001Block074Part024SupportExplicit : Finset ℕ :=
  ([27802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block074Part024 : ℚ :=
  (193237801 : ℚ) / 1493502804832800

def SurrogateDiagonalTailChunk001Sub001Block074Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27802
    = surrogateDiagTailX0RatChunk001Sub001Block074Part024

theorem surrogateDiagonalTailChunk001Sub001Block074Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block074Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block074Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block074Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block074Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block074Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block074HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block074Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block074Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block074Part000
    + surrogateDiagTailX0RatChunk001Sub001Block074Part001
    + surrogateDiagTailX0RatChunk001Sub001Block074Part002
    + surrogateDiagTailX0RatChunk001Sub001Block074Part003
    + surrogateDiagTailX0RatChunk001Sub001Block074Part004
    + surrogateDiagTailX0RatChunk001Sub001Block074Part005
    + surrogateDiagTailX0RatChunk001Sub001Block074Part006
    + surrogateDiagTailX0RatChunk001Sub001Block074Part007
    + surrogateDiagTailX0RatChunk001Sub001Block074Part008
    + surrogateDiagTailX0RatChunk001Sub001Block074Part009

def surrogateDiagonalTailChunk001Sub001Block074MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block074Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block074Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block074Part010
    + surrogateDiagTailX0RatChunk001Sub001Block074Part011
    + surrogateDiagTailX0RatChunk001Sub001Block074Part012
    + surrogateDiagTailX0RatChunk001Sub001Block074Part013
    + surrogateDiagTailX0RatChunk001Sub001Block074Part014
    + surrogateDiagTailX0RatChunk001Sub001Block074Part015
    + surrogateDiagTailX0RatChunk001Sub001Block074Part016
    + surrogateDiagTailX0RatChunk001Sub001Block074Part017
    + surrogateDiagTailX0RatChunk001Sub001Block074Part018
    + surrogateDiagTailX0RatChunk001Sub001Block074Part019

def surrogateDiagonalTailChunk001Sub001Block074TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block074Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block074Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block074Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block074Part020
    + surrogateDiagTailX0RatChunk001Sub001Block074Part021
    + surrogateDiagTailX0RatChunk001Sub001Block074Part022
    + surrogateDiagTailX0RatChunk001Sub001Block074Part023
    + surrogateDiagTailX0RatChunk001Sub001Block074Part024

def surrogateDiagonalTailChunk001Sub001Block074Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block074HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block074MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block074TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block074 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block074Part000
    + surrogateDiagTailX0RatChunk001Sub001Block074Part001
    + surrogateDiagTailX0RatChunk001Sub001Block074Part002
    + surrogateDiagTailX0RatChunk001Sub001Block074Part003
    + surrogateDiagTailX0RatChunk001Sub001Block074Part004
    + surrogateDiagTailX0RatChunk001Sub001Block074Part005
    + surrogateDiagTailX0RatChunk001Sub001Block074Part006
    + surrogateDiagTailX0RatChunk001Sub001Block074Part007
    + surrogateDiagTailX0RatChunk001Sub001Block074Part008
    + surrogateDiagTailX0RatChunk001Sub001Block074Part009
    + surrogateDiagTailX0RatChunk001Sub001Block074Part010
    + surrogateDiagTailX0RatChunk001Sub001Block074Part011
    + surrogateDiagTailX0RatChunk001Sub001Block074Part012
    + surrogateDiagTailX0RatChunk001Sub001Block074Part013
    + surrogateDiagTailX0RatChunk001Sub001Block074Part014
    + surrogateDiagTailX0RatChunk001Sub001Block074Part015
    + surrogateDiagTailX0RatChunk001Sub001Block074Part016
    + surrogateDiagTailX0RatChunk001Sub001Block074Part017
    + surrogateDiagTailX0RatChunk001Sub001Block074Part018
    + surrogateDiagTailX0RatChunk001Sub001Block074Part019
    + surrogateDiagTailX0RatChunk001Sub001Block074Part020
    + surrogateDiagTailX0RatChunk001Sub001Block074Part021
    + surrogateDiagTailX0RatChunk001Sub001Block074Part022
    + surrogateDiagTailX0RatChunk001Sub001Block074Part023
    + surrogateDiagTailX0RatChunk001Sub001Block074Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block074_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block074Head + surrogateDiagTailX0RatChunk001Sub001Block074Mid + surrogateDiagTailX0RatChunk001Sub001Block074Tail =
      surrogateDiagTailX0RatChunk001Sub001Block074 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block074Head surrogateDiagTailX0RatChunk001Sub001Block074Mid surrogateDiagTailX0RatChunk001Sub001Block074Tail surrogateDiagTailX0RatChunk001Sub001Block074
  ring

def SurrogateDiagonalTailChunk001Sub001Block074HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block074HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block074Head

def SurrogateDiagonalTailChunk001Sub001Block074MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block074MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block074Mid

def SurrogateDiagonalTailChunk001Sub001Block074TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block074TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block074Tail

theorem surrogateDiagonalTailChunk001Sub001Block074_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block074HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block074MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block074TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block074Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block074 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block074HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block074MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block074TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block074Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block074_eq_head_add_mid_add_tail

/-- Block 075 covers tail-support indices [16875,16900) and q from 27803 to 27842. -/

def TailChunk001Sub001Block075Part000SupportExplicit : Finset ℕ :=
  ([27803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part000 : ℚ :=
  (12078231390625 : ℚ) / 373483159048626641202

def SurrogateDiagonalTailChunk001Sub001Block075Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27803
    = surrogateDiagTailX0RatChunk001Sub001Block075Part000

theorem surrogateDiagonalTailChunk001Sub001Block075Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part000] using hcert

def TailChunk001Sub001Block075Part001SupportExplicit : Finset ℕ :=
  ([27805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part001 : ℚ :=
  (1636784586925 : ℚ) / 30508824227777888256

def SurrogateDiagonalTailChunk001Sub001Block075Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27805
    = surrogateDiagTailX0RatChunk001Sub001Block075Part001

theorem surrogateDiagonalTailChunk001Sub001Block075Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part001] using hcert

def TailChunk001Sub001Block075Part002SupportExplicit : Finset ℕ :=
  ([27806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part002 : ℚ :=
  (3020209515625 : ℚ) / 23349415005139195602

def SurrogateDiagonalTailChunk001Sub001Block075Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27806
    = surrogateDiagTailX0RatChunk001Sub001Block075Part002

theorem surrogateDiagonalTailChunk001Sub001Block075Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part002] using hcert

def TailChunk001Sub001Block075Part003SupportExplicit : Finset ℕ :=
  ([27807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part003 : ℚ :=
  (163301857333 : ℚ) / 1574155270884556800

def SurrogateDiagonalTailChunk001Sub001Block075Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27807
    = surrogateDiagTailX0RatChunk001Sub001Block075Part003

theorem surrogateDiagonalTailChunk001Sub001Block075Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part003] using hcert

def TailChunk001Sub001Block075Part004SupportExplicit : Finset ℕ :=
  ([27809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part004 : ℚ :=
  (12083445015625 : ℚ) / 373805671742297997312

def SurrogateDiagonalTailChunk001Sub001Block075Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27809
    = surrogateDiagTailX0RatChunk001Sub001Block075Part004

theorem surrogateDiagonalTailChunk001Sub001Block075Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part004] using hcert

def TailChunk001Sub001Block075Part005SupportExplicit : Finset ℕ :=
  ([27811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part005 : ℚ :=
  (16893376740425 : ℚ) / 340713721047709384704

def SurrogateDiagonalTailChunk001Sub001Block075Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27811
    = surrogateDiagTailX0RatChunk001Sub001Block075Part005

theorem surrogateDiagonalTailChunk001Sub001Block075Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part005] using hcert

def TailChunk001Sub001Block075Part006SupportExplicit : Finset ℕ :=
  ([27813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part006 : ℚ :=
  (20691227399125 : ℚ) / 270993583391176654848

def SurrogateDiagonalTailChunk001Sub001Block075Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27813
    = surrogateDiagTailX0RatChunk001Sub001Block075Part006

theorem surrogateDiagonalTailChunk001Sub001Block075Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part006] using hcert

def TailChunk001Sub001Block075Part007SupportExplicit : Finset ℕ :=
  ([27814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part007 : ℚ :=
  (3021947640625 : ℚ) / 23376299763444481362

def SurrogateDiagonalTailChunk001Sub001Block075Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27814
    = surrogateDiagTailX0RatChunk001Sub001Block075Part007

theorem surrogateDiagonalTailChunk001Sub001Block075Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part007] using hcert

def TailChunk001Sub001Block075Part008SupportExplicit : Finset ℕ :=
  ([27815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part008 : ℚ :=
  (644522796875 : ℚ) / 12762904657081792896

def SurrogateDiagonalTailChunk001Sub001Block075Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27815
    = surrogateDiagTailX0RatChunk001Sub001Block075Part008

theorem surrogateDiagonalTailChunk001Sub001Block075Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part008] using hcert

def TailChunk001Sub001Block075Part009SupportExplicit : Finset ℕ :=
  ([27817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part009 : ℚ :=
  (12090398265625 : ℚ) / 374236013527371182592

def SurrogateDiagonalTailChunk001Sub001Block075Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27817
    = surrogateDiagTailX0RatChunk001Sub001Block075Part009

theorem surrogateDiagonalTailChunk001Sub001Block075Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part009] using hcert

def TailChunk001Sub001Block075Part010SupportExplicit : Finset ℕ :=
  ([27818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part010 : ℚ :=
  (73206415625 : ℚ) / 393857271015467481

def SurrogateDiagonalTailChunk001Sub001Block075Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27818
    = surrogateDiagTailX0RatChunk001Sub001Block075Part010

theorem surrogateDiagonalTailChunk001Sub001Block075Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part010] using hcert

def TailChunk001Sub001Block075Part011SupportExplicit : Finset ℕ :=
  ([27821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part011 : ℚ :=
  (2887975408525 : ℚ) / 84690385514561719368

def SurrogateDiagonalTailChunk001Sub001Block075Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27821
    = surrogateDiagTailX0RatChunk001Sub001Block075Part011

theorem surrogateDiagonalTailChunk001Sub001Block075Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part011] using hcert

def TailChunk001Sub001Block075Part012SupportExplicit : Finset ℕ :=
  ([27822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part012 : ℚ :=
  (5373748536325 : ℚ) / 18480790791475120128

def SurrogateDiagonalTailChunk001Sub001Block075Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27822
    = surrogateDiagTailX0RatChunk001Sub001Block075Part012

theorem surrogateDiagonalTailChunk001Sub001Block075Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part012] using hcert

def TailChunk001Sub001Block075Part013SupportExplicit : Finset ℕ :=
  ([27823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part013 : ℚ :=
  (12095614515625 : ℚ) / 374559013628143366482

def SurrogateDiagonalTailChunk001Sub001Block075Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27823
    = surrogateDiagTailX0RatChunk001Sub001Block075Part013

theorem surrogateDiagonalTailChunk001Sub001Block075Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part013] using hcert

def TailChunk001Sub001Block075Part014SupportExplicit : Finset ℕ :=
  ([27826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part014 : ℚ :=
  (3024555765625 : ℚ) / 23416670423566152192

def SurrogateDiagonalTailChunk001Sub001Block075Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27826
    = surrogateDiagTailX0RatChunk001Sub001Block075Part014

theorem surrogateDiagonalTailChunk001Sub001Block075Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part014] using hcert

def TailChunk001Sub001Block075Part015SupportExplicit : Finset ℕ :=
  ([27827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part015 : ℚ :=
  (12099092640625 : ℚ) / 374774463155867853522

def SurrogateDiagonalTailChunk001Sub001Block075Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27827
    = surrogateDiagTailX0RatChunk001Sub001Block075Part015

theorem surrogateDiagonalTailChunk001Sub001Block075Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part015] using hcert

def TailChunk001Sub001Block075Part016SupportExplicit : Finset ℕ :=
  ([27829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part016 : ℚ :=
  (10791386401375 : ℚ) / 293481003588960387072

def SurrogateDiagonalTailChunk001Sub001Block075Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27829
    = surrogateDiagTailX0RatChunk001Sub001Block075Part016

theorem surrogateDiagonalTailChunk001Sub001Block075Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part016] using hcert

def TailChunk001Sub001Block075Part017SupportExplicit : Finset ℕ :=
  ([27831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part017 : ℚ :=
  (21511668072325 : ℚ) / 296203237742547191808

def SurrogateDiagonalTailChunk001Sub001Block075Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27831
    = surrogateDiagTailX0RatChunk001Sub001Block075Part017

theorem surrogateDiagonalTailChunk001Sub001Block075Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part017] using hcert

def TailChunk001Sub001Block075Part018SupportExplicit : Finset ℕ :=
  ([27833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part018 : ℚ :=
  (553436532617 : ℚ) / 14499254504838758400

def SurrogateDiagonalTailChunk001Sub001Block075Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27833
    = surrogateDiagTailX0RatChunk001Sub001Block075Part018

theorem surrogateDiagonalTailChunk001Sub001Block075Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part018] using hcert

def TailChunk001Sub001Block075Part019SupportExplicit : Finset ℕ :=
  ([27834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part019 : ℚ :=
  (5378385536125 : ℚ) / 18512702358909199488

def SurrogateDiagonalTailChunk001Sub001Block075Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27834
    = surrogateDiagTailX0RatChunk001Sub001Block075Part019

theorem surrogateDiagonalTailChunk001Sub001Block075Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part019] using hcert

def TailChunk001Sub001Block075Part020SupportExplicit : Finset ℕ :=
  ([27835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part020 : ℚ :=
  (27891664502125 : ℚ) / 488526638934498213888

def SurrogateDiagonalTailChunk001Sub001Block075Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27835
    = surrogateDiagTailX0RatChunk001Sub001Block075Part020

theorem surrogateDiagonalTailChunk001Sub001Block075Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part020] using hcert

def TailChunk001Sub001Block075Part021SupportExplicit : Finset ℕ :=
  ([27838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part021 : ℚ :=
  (91404931937 : ℚ) / 652700462968995840

def SurrogateDiagonalTailChunk001Sub001Block075Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27838
    = surrogateDiagTailX0RatChunk001Sub001Block075Part021

theorem surrogateDiagonalTailChunk001Sub001Block075Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part021] using hcert

def TailChunk001Sub001Block075Part022SupportExplicit : Finset ℕ :=
  ([27839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part022 : ℚ :=
  (14843184067 : ℚ) / 313165736501575680

def SurrogateDiagonalTailChunk001Sub001Block075Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27839
    = surrogateDiagTailX0RatChunk001Sub001Block075Part022

theorem surrogateDiagonalTailChunk001Sub001Block075Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part022] using hcert

def TailChunk001Sub001Block075Part023SupportExplicit : Finset ℕ :=
  ([27841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part023 : ℚ :=
  (161641603261 : ℚ) / 4097971511416200000

def SurrogateDiagonalTailChunk001Sub001Block075Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27841
    = surrogateDiagTailX0RatChunk001Sub001Block075Part023

theorem surrogateDiagonalTailChunk001Sub001Block075Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part023] using hcert

def TailChunk001Sub001Block075Part024SupportExplicit : Finset ℕ :=
  ([27842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block075Part024 : ℚ :=
  (4844856025 : ℚ) / 37552926852513792

def SurrogateDiagonalTailChunk001Sub001Block075Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27842
    = surrogateDiagTailX0RatChunk001Sub001Block075Part024

theorem surrogateDiagonalTailChunk001Sub001Block075Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block075Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block075Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block075Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block075Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block075Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block075HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block075Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block075Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block075Part000
    + surrogateDiagTailX0RatChunk001Sub001Block075Part001
    + surrogateDiagTailX0RatChunk001Sub001Block075Part002
    + surrogateDiagTailX0RatChunk001Sub001Block075Part003
    + surrogateDiagTailX0RatChunk001Sub001Block075Part004
    + surrogateDiagTailX0RatChunk001Sub001Block075Part005
    + surrogateDiagTailX0RatChunk001Sub001Block075Part006
    + surrogateDiagTailX0RatChunk001Sub001Block075Part007
    + surrogateDiagTailX0RatChunk001Sub001Block075Part008
    + surrogateDiagTailX0RatChunk001Sub001Block075Part009

def surrogateDiagonalTailChunk001Sub001Block075MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block075Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block075Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block075Part010
    + surrogateDiagTailX0RatChunk001Sub001Block075Part011
    + surrogateDiagTailX0RatChunk001Sub001Block075Part012
    + surrogateDiagTailX0RatChunk001Sub001Block075Part013
    + surrogateDiagTailX0RatChunk001Sub001Block075Part014
    + surrogateDiagTailX0RatChunk001Sub001Block075Part015
    + surrogateDiagTailX0RatChunk001Sub001Block075Part016
    + surrogateDiagTailX0RatChunk001Sub001Block075Part017
    + surrogateDiagTailX0RatChunk001Sub001Block075Part018
    + surrogateDiagTailX0RatChunk001Sub001Block075Part019

def surrogateDiagonalTailChunk001Sub001Block075TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block075Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block075Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block075Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block075Part020
    + surrogateDiagTailX0RatChunk001Sub001Block075Part021
    + surrogateDiagTailX0RatChunk001Sub001Block075Part022
    + surrogateDiagTailX0RatChunk001Sub001Block075Part023
    + surrogateDiagTailX0RatChunk001Sub001Block075Part024

def surrogateDiagonalTailChunk001Sub001Block075Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block075HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block075MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block075TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block075 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block075Part000
    + surrogateDiagTailX0RatChunk001Sub001Block075Part001
    + surrogateDiagTailX0RatChunk001Sub001Block075Part002
    + surrogateDiagTailX0RatChunk001Sub001Block075Part003
    + surrogateDiagTailX0RatChunk001Sub001Block075Part004
    + surrogateDiagTailX0RatChunk001Sub001Block075Part005
    + surrogateDiagTailX0RatChunk001Sub001Block075Part006
    + surrogateDiagTailX0RatChunk001Sub001Block075Part007
    + surrogateDiagTailX0RatChunk001Sub001Block075Part008
    + surrogateDiagTailX0RatChunk001Sub001Block075Part009
    + surrogateDiagTailX0RatChunk001Sub001Block075Part010
    + surrogateDiagTailX0RatChunk001Sub001Block075Part011
    + surrogateDiagTailX0RatChunk001Sub001Block075Part012
    + surrogateDiagTailX0RatChunk001Sub001Block075Part013
    + surrogateDiagTailX0RatChunk001Sub001Block075Part014
    + surrogateDiagTailX0RatChunk001Sub001Block075Part015
    + surrogateDiagTailX0RatChunk001Sub001Block075Part016
    + surrogateDiagTailX0RatChunk001Sub001Block075Part017
    + surrogateDiagTailX0RatChunk001Sub001Block075Part018
    + surrogateDiagTailX0RatChunk001Sub001Block075Part019
    + surrogateDiagTailX0RatChunk001Sub001Block075Part020
    + surrogateDiagTailX0RatChunk001Sub001Block075Part021
    + surrogateDiagTailX0RatChunk001Sub001Block075Part022
    + surrogateDiagTailX0RatChunk001Sub001Block075Part023
    + surrogateDiagTailX0RatChunk001Sub001Block075Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block075_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block075Head + surrogateDiagTailX0RatChunk001Sub001Block075Mid + surrogateDiagTailX0RatChunk001Sub001Block075Tail =
      surrogateDiagTailX0RatChunk001Sub001Block075 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block075Head surrogateDiagTailX0RatChunk001Sub001Block075Mid surrogateDiagTailX0RatChunk001Sub001Block075Tail surrogateDiagTailX0RatChunk001Sub001Block075
  ring

def SurrogateDiagonalTailChunk001Sub001Block075HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block075HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block075Head

def SurrogateDiagonalTailChunk001Sub001Block075MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block075MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block075Mid

def SurrogateDiagonalTailChunk001Sub001Block075TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block075TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block075Tail

theorem surrogateDiagonalTailChunk001Sub001Block075_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block075HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block075MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block075TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block075Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block075 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block075HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block075MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block075TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block075Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block075_eq_head_add_mid_add_tail

/-- Block 076 covers tail-support indices [16900,16925) and q from 27843 to 27887. -/

def TailChunk001Sub001Block076Part000SupportExplicit : Finset ℕ :=
  ([27843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part000 : ℚ :=
  (861208962877 : ℚ) / 11868579350917939200

def SurrogateDiagonalTailChunk001Sub001Block076Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27843
    = surrogateDiagTailX0RatChunk001Sub001Block076Part000

theorem surrogateDiagonalTailChunk001Sub001Block076Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part000] using hcert

def TailChunk001Sub001Block076Part001SupportExplicit : Finset ℕ :=
  ([27845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part001 : ℚ :=
  (645914046875 : ℚ) / 12818065698991374336

def SurrogateDiagonalTailChunk001Sub001Block076Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27845
    = surrogateDiagTailX0RatChunk001Sub001Block076Part001

theorem surrogateDiagonalTailChunk001Sub001Block076Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part001] using hcert

def TailChunk001Sub001Block076Part002SupportExplicit : Finset ℕ :=
  ([27847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part002 : ℚ :=
  (12116490765625 : ℚ) / 375853105322997020082

def SurrogateDiagonalTailChunk001Sub001Block076Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27847
    = surrogateDiagTailX0RatChunk001Sub001Block076Part002

theorem surrogateDiagonalTailChunk001Sub001Block076Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part002] using hcert

def TailChunk001Sub001Block076Part003SupportExplicit : Finset ℕ :=
  ([27849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part003 : ℚ :=
  (21539505071725 : ℚ) / 296970354823108756608

def SurrogateDiagonalTailChunk001Sub001Block076Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27849
    = surrogateDiagTailX0RatChunk001Sub001Block076Part003

theorem surrogateDiagonalTailChunk001Sub001Block076Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part003] using hcert

def TailChunk001Sub001Block076Part004SupportExplicit : Finset ℕ :=
  ([27851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part004 : ℚ :=
  (775678201 : ℚ) / 24068423222350050

def SurrogateDiagonalTailChunk001Sub001Block076Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27851
    = surrogateDiagTailX0RatChunk001Sub001Block076Part004

theorem surrogateDiagonalTailChunk001Sub001Block076Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part004] using hcert

def TailChunk001Sub001Block076Part005SupportExplicit : Finset ℕ :=
  ([27853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part005 : ℚ :=
  (904657882675 : ℚ) / 18455842298543874048

def SurrogateDiagonalTailChunk001Sub001Block076Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27853
    = surrogateDiagTailX0RatChunk001Sub001Block076Part005

theorem surrogateDiagonalTailChunk001Sub001Block076Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part005] using hcert

def TailChunk001Sub001Block076Part006SupportExplicit : Finset ℕ :=
  ([27854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part006 : ℚ :=
  (5512275516425 : ℚ) / 37681762490359686144

def SurrogateDiagonalTailChunk001Sub001Block076Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27854
    = surrogateDiagTailX0RatChunk001Sub001Block076Part006

theorem surrogateDiagonalTailChunk001Sub001Block076Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part006] using hcert

def TailChunk001Sub001Block076Part007SupportExplicit : Finset ℕ :=
  ([27857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part007 : ℚ :=
  (11809032449875 : ℚ) / 355235150156909248512

def SurrogateDiagonalTailChunk001Sub001Block076Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27857
    = surrogateDiagTailX0RatChunk001Sub001Block076Part007

theorem surrogateDiagonalTailChunk001Sub001Block076Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part007] using hcert

def TailChunk001Sub001Block076Part008SupportExplicit : Finset ℕ :=
  ([27858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part008 : ℚ :=
  (489787775975 : ℚ) / 1688786314346364288

def SurrogateDiagonalTailChunk001Sub001Block076Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27858
    = surrogateDiagTailX0RatChunk001Sub001Block076Part008

theorem surrogateDiagonalTailChunk001Sub001Block076Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part008] using hcert

def TailChunk001Sub001Block076Part009SupportExplicit : Finset ℕ :=
  ([27859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part009 : ℚ :=
  (41585353761625 : ℚ) / 1091515001852549449728

def SurrogateDiagonalTailChunk001Sub001Block076Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27859
    = surrogateDiagTailX0RatChunk001Sub001Block076Part009

theorem surrogateDiagonalTailChunk001Sub001Block076Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part009] using hcert

def TailChunk001Sub001Block076Part010SupportExplicit : Finset ℕ :=
  ([27861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part010 : ℚ :=
  (18133963459 : ℚ) / 233326656000000000

def SurrogateDiagonalTailChunk001Sub001Block076Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27861
    = surrogateDiagTailX0RatChunk001Sub001Block076Part010

theorem surrogateDiagonalTailChunk001Sub001Block076Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part010] using hcert

def TailChunk001Sub001Block076Part011SupportExplicit : Finset ℕ :=
  ([27862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part011 : ℚ :=
  (4851819025 : ℚ) / 37660953900653202

def SurrogateDiagonalTailChunk001Sub001Block076Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27862
    = surrogateDiagTailX0RatChunk001Sub001Block076Part011

theorem surrogateDiagonalTailChunk001Sub001Block076Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part011] using hcert

def TailChunk001Sub001Block076Part012SupportExplicit : Finset ℕ :=
  ([27863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part012 : ℚ :=
  (14900464839 : ℚ) / 327598880797491200

def SurrogateDiagonalTailChunk001Sub001Block076Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27863
    = surrogateDiagTailX0RatChunk001Sub001Block076Part012

theorem surrogateDiagonalTailChunk001Sub001Block076Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part012] using hcert

def TailChunk001Sub001Block076Part013SupportExplicit : Finset ℕ :=
  ([27865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part013 : ℚ :=
  (1940527140625 : ℚ) / 38564816794268878848

def SurrogateDiagonalTailChunk001Sub001Block076Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27865
    = surrogateDiagTailX0RatChunk001Sub001Block076Part013

theorem surrogateDiagonalTailChunk001Sub001Block076Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part013] using hcert

def TailChunk001Sub001Block076Part014SupportExplicit : Finset ℕ :=
  ([27866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part014 : ℚ :=
  (3033257640625 : ℚ) / 23551617029773008672

def SurrogateDiagonalTailChunk001Sub001Block076Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27866
    = surrogateDiagTailX0RatChunk001Sub001Block076Part014

theorem surrogateDiagonalTailChunk001Sub001Block076Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part014] using hcert

def TailChunk001Sub001Block076Part015SupportExplicit : Finset ℕ :=
  ([27867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part015 : ℚ :=
  (1795131044975 : ℚ) / 17810800122668746752

def SurrogateDiagonalTailChunk001Sub001Block076Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27867
    = surrogateDiagTailX0RatChunk001Sub001Block076Part015

theorem surrogateDiagonalTailChunk001Sub001Block076Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part015] using hcert

def TailChunk001Sub001Block076Part016SupportExplicit : Finset ℕ :=
  ([27870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part016 : ℚ :=
  (3823888566925 : ℚ) / 7595890784587481088

def SurrogateDiagonalTailChunk001Sub001Block076Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27870
    = surrogateDiagTailX0RatChunk001Sub001Block076Part016

theorem surrogateDiagonalTailChunk001Sub001Block076Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part016] using hcert

def TailChunk001Sub001Block076Part017SupportExplicit : Finset ℕ :=
  ([27871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part017 : ℚ :=
  (505641199025 : ℚ) / 14947108434986532864

def SurrogateDiagonalTailChunk001Sub001Block076Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27871
    = surrogateDiagTailX0RatChunk001Sub001Block076Part017

theorem surrogateDiagonalTailChunk001Sub001Block076Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part017] using hcert

def TailChunk001Sub001Block076Part018SupportExplicit : Finset ℕ :=
  ([27874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part018 : ℚ :=
  (311064764263 : ℚ) / 1360761057792000000

def SurrogateDiagonalTailChunk001Sub001Block076Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27874
    = surrogateDiagTailX0RatChunk001Sub001Block076Part018

theorem surrogateDiagonalTailChunk001Sub001Block076Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part018] using hcert

def TailChunk001Sub001Block076Part019SupportExplicit : Finset ℕ :=
  ([27877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part019 : ℚ :=
  (938739053417 : ℚ) / 28023425866668441600

def SurrogateDiagonalTailChunk001Sub001Block076Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27877
    = surrogateDiagTailX0RatChunk001Sub001Block076Part019

theorem surrogateDiagonalTailChunk001Sub001Block076Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part019] using hcert

def TailChunk001Sub001Block076Part020SupportExplicit : Finset ℕ :=
  ([27878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part020 : ℚ :=
  (1461949868075 : ℚ) / 10768504942246062336

def SurrogateDiagonalTailChunk001Sub001Block076Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27878
    = surrogateDiagTailX0RatChunk001Sub001Block076Part020

theorem surrogateDiagonalTailChunk001Sub001Block076Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part020] using hcert

def TailChunk001Sub001Block076Part021SupportExplicit : Finset ℕ :=
  ([27879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part021 : ℚ :=
  (21585940070725 : ℚ) / 298252193275660781568

def SurrogateDiagonalTailChunk001Sub001Block076Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27879
    = surrogateDiagTailX0RatChunk001Sub001Block076Part021

theorem surrogateDiagonalTailChunk001Sub001Block076Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part021] using hcert

def TailChunk001Sub001Block076Part022SupportExplicit : Finset ℕ :=
  ([27883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part022 : ℚ :=
  (12147838890625 : ℚ) / 377800526665267396722

def SurrogateDiagonalTailChunk001Sub001Block076Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27883
    = surrogateDiagTailX0RatChunk001Sub001Block076Part022

theorem surrogateDiagonalTailChunk001Sub001Block076Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part022] using hcert

def TailChunk001Sub001Block076Part023SupportExplicit : Finset ℕ :=
  ([27886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part023 : ℚ :=
  (47104641247 : ℚ) / 350292823333355520

def SurrogateDiagonalTailChunk001Sub001Block076Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27886
    = surrogateDiagTailX0RatChunk001Sub001Block076Part023

theorem surrogateDiagonalTailChunk001Sub001Block076Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part023] using hcert

def TailChunk001Sub001Block076Part024SupportExplicit : Finset ℕ :=
  ([27887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block076Part024 : ℚ :=
  (23620952217875 : ℚ) / 710470300313818497024

def SurrogateDiagonalTailChunk001Sub001Block076Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27887
    = surrogateDiagTailX0RatChunk001Sub001Block076Part024

theorem surrogateDiagonalTailChunk001Sub001Block076Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block076Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block076Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block076Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block076Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block076Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block076HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block076Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block076Part000
    + surrogateDiagTailX0RatChunk001Sub001Block076Part001
    + surrogateDiagTailX0RatChunk001Sub001Block076Part002
    + surrogateDiagTailX0RatChunk001Sub001Block076Part003
    + surrogateDiagTailX0RatChunk001Sub001Block076Part004
    + surrogateDiagTailX0RatChunk001Sub001Block076Part005
    + surrogateDiagTailX0RatChunk001Sub001Block076Part006
    + surrogateDiagTailX0RatChunk001Sub001Block076Part007
    + surrogateDiagTailX0RatChunk001Sub001Block076Part008
    + surrogateDiagTailX0RatChunk001Sub001Block076Part009

def surrogateDiagonalTailChunk001Sub001Block076MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block076Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block076Part010
    + surrogateDiagTailX0RatChunk001Sub001Block076Part011
    + surrogateDiagTailX0RatChunk001Sub001Block076Part012
    + surrogateDiagTailX0RatChunk001Sub001Block076Part013
    + surrogateDiagTailX0RatChunk001Sub001Block076Part014
    + surrogateDiagTailX0RatChunk001Sub001Block076Part015
    + surrogateDiagTailX0RatChunk001Sub001Block076Part016
    + surrogateDiagTailX0RatChunk001Sub001Block076Part017
    + surrogateDiagTailX0RatChunk001Sub001Block076Part018
    + surrogateDiagTailX0RatChunk001Sub001Block076Part019

def surrogateDiagonalTailChunk001Sub001Block076TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block076Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block076Part020
    + surrogateDiagTailX0RatChunk001Sub001Block076Part021
    + surrogateDiagTailX0RatChunk001Sub001Block076Part022
    + surrogateDiagTailX0RatChunk001Sub001Block076Part023
    + surrogateDiagTailX0RatChunk001Sub001Block076Part024

def surrogateDiagonalTailChunk001Sub001Block076Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block076HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block076MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block076TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block076 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block076Part000
    + surrogateDiagTailX0RatChunk001Sub001Block076Part001
    + surrogateDiagTailX0RatChunk001Sub001Block076Part002
    + surrogateDiagTailX0RatChunk001Sub001Block076Part003
    + surrogateDiagTailX0RatChunk001Sub001Block076Part004
    + surrogateDiagTailX0RatChunk001Sub001Block076Part005
    + surrogateDiagTailX0RatChunk001Sub001Block076Part006
    + surrogateDiagTailX0RatChunk001Sub001Block076Part007
    + surrogateDiagTailX0RatChunk001Sub001Block076Part008
    + surrogateDiagTailX0RatChunk001Sub001Block076Part009
    + surrogateDiagTailX0RatChunk001Sub001Block076Part010
    + surrogateDiagTailX0RatChunk001Sub001Block076Part011
    + surrogateDiagTailX0RatChunk001Sub001Block076Part012
    + surrogateDiagTailX0RatChunk001Sub001Block076Part013
    + surrogateDiagTailX0RatChunk001Sub001Block076Part014
    + surrogateDiagTailX0RatChunk001Sub001Block076Part015
    + surrogateDiagTailX0RatChunk001Sub001Block076Part016
    + surrogateDiagTailX0RatChunk001Sub001Block076Part017
    + surrogateDiagTailX0RatChunk001Sub001Block076Part018
    + surrogateDiagTailX0RatChunk001Sub001Block076Part019
    + surrogateDiagTailX0RatChunk001Sub001Block076Part020
    + surrogateDiagTailX0RatChunk001Sub001Block076Part021
    + surrogateDiagTailX0RatChunk001Sub001Block076Part022
    + surrogateDiagTailX0RatChunk001Sub001Block076Part023
    + surrogateDiagTailX0RatChunk001Sub001Block076Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block076_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block076Head + surrogateDiagTailX0RatChunk001Sub001Block076Mid + surrogateDiagTailX0RatChunk001Sub001Block076Tail =
      surrogateDiagTailX0RatChunk001Sub001Block076 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block076Head surrogateDiagTailX0RatChunk001Sub001Block076Mid surrogateDiagTailX0RatChunk001Sub001Block076Tail surrogateDiagTailX0RatChunk001Sub001Block076
  ring

def SurrogateDiagonalTailChunk001Sub001Block076HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block076HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block076Head

def SurrogateDiagonalTailChunk001Sub001Block076MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block076MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block076Mid

def SurrogateDiagonalTailChunk001Sub001Block076TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block076TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block076Tail

theorem surrogateDiagonalTailChunk001Sub001Block076_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block076HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block076MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block076TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block076Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block076 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block076HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block076MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block076TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block076Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block076_eq_head_add_mid_add_tail

/-- Block 077 covers tail-support indices [16925,16950) and q from 27890 to 27929. -/

def TailChunk001Sub001Block077Part000SupportExplicit : Finset ℕ :=
  ([27890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part000 : ℚ :=
  (8260780690975 : ℚ) / 38675674981645713408

def SurrogateDiagonalTailChunk001Sub001Block077Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27890
    = surrogateDiagTailX0RatChunk001Sub001Block077Part000

theorem surrogateDiagonalTailChunk001Sub001Block077Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part000] using hcert

def TailChunk001Sub001Block077Part001SupportExplicit : Finset ℕ :=
  ([27893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part001 : ℚ :=
  (12156553890625 : ℚ) / 378342817498003598112

def SurrogateDiagonalTailChunk001Sub001Block077Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27893
    = surrogateDiagTailX0RatChunk001Sub001Block077Part001

theorem surrogateDiagonalTailChunk001Sub001Block077Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part001] using hcert

def TailChunk001Sub001Block077Part002SupportExplicit : Finset ℕ :=
  ([27894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part002 : ℚ :=
  (5401600535125 : ℚ) / 18672880550992969728

def SurrogateDiagonalTailChunk001Sub001Block077Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27894
    = surrogateDiagTailX0RatChunk001Sub001Block077Part002

theorem surrogateDiagonalTailChunk001Sub001Block077Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part002] using hcert

def TailChunk001Sub001Block077Part003SupportExplicit : Finset ℕ :=
  ([27895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part003 : ℚ :=
  (5753394244675 : ℚ) / 83265310396288991232

def SurrogateDiagonalTailChunk001Sub001Block077Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27895
    = surrogateDiagTailX0RatChunk001Sub001Block077Part003

theorem surrogateDiagonalTailChunk001Sub001Block077Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part003] using hcert

def TailChunk001Sub001Block077Part004SupportExplicit : Finset ℕ :=
  ([27897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part004 : ℚ :=
  (9674876735675 : ℚ) / 116511112017859313664

def SurrogateDiagonalTailChunk001Sub001Block077Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27897
    = surrogateDiagTailX0RatChunk001Sub001Block077Part004

theorem surrogateDiagonalTailChunk001Sub001Block077Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part004] using hcert

def TailChunk001Sub001Block077Part005SupportExplicit : Finset ℕ :=
  ([27898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part005 : ℚ :=
  (1201264323725 : ℚ) / 6691199589905596416

def SurrogateDiagonalTailChunk001Sub001Block077Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27898
    = surrogateDiagTailX0RatChunk001Sub001Block077Part005

theorem surrogateDiagonalTailChunk001Sub001Block077Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part005] using hcert

def TailChunk001Sub001Block077Part006SupportExplicit : Finset ℕ :=
  ([27899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part006 : ℚ :=
  (2032732457275 : ℚ) / 57452030276553944064

def SurrogateDiagonalTailChunk001Sub001Block077Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27899
    = surrogateDiagTailX0RatChunk001Sub001Block077Part006

theorem surrogateDiagonalTailChunk001Sub001Block077Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part006] using hcert

def TailChunk001Sub001Block077Part007SupportExplicit : Finset ℕ :=
  ([27901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part007 : ℚ :=
  (778465801 : ℚ) / 24241732501024800

def SurrogateDiagonalTailChunk001Sub001Block077Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27901
    = surrogateDiagTailX0RatChunk001Sub001Block077Part007

theorem surrogateDiagonalTailChunk001Sub001Block077Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part007] using hcert

def TailChunk001Sub001Block077Part008SupportExplicit : Finset ℕ :=
  ([27902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part008 : ℚ :=
  (2356778564875 : ℚ) / 12756431621726871552

def SurrogateDiagonalTailChunk001Sub001Block077Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27902
    = surrogateDiagTailX0RatChunk001Sub001Block077Part008

theorem surrogateDiagonalTailChunk001Sub001Block077Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part008] using hcert

def TailChunk001Sub001Block077Part009SupportExplicit : Finset ℕ :=
  ([27903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part009 : ℚ :=
  (59480215181 : ℚ) / 783870582768000000

def SurrogateDiagonalTailChunk001Sub001Block077Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27903
    = surrogateDiagTailX0RatChunk001Sub001Block077Part009

theorem surrogateDiagonalTailChunk001Sub001Block077Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part009] using hcert

def TailChunk001Sub001Block077Part010SupportExplicit : Finset ℕ :=
  ([27905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part010 : ℚ :=
  (1037921675 : ℚ) / 20686278400874496

def SurrogateDiagonalTailChunk001Sub001Block077Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27905
    = surrogateDiagTailX0RatChunk001Sub001Block077Part010

theorem surrogateDiagonalTailChunk001Sub001Block077Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part010] using hcert

def TailChunk001Sub001Block077Part011SupportExplicit : Finset ℕ :=
  ([27906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part011 : ℚ :=
  (216249981397 : ℚ) / 748201620402000000

def SurrogateDiagonalTailChunk001Sub001Block077Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27906
    = surrogateDiagTailX0RatChunk001Sub001Block077Part011

theorem surrogateDiagonalTailChunk001Sub001Block077Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part011] using hcert

def TailChunk001Sub001Block077Part012SupportExplicit : Finset ℕ :=
  ([27907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part012 : ℚ :=
  (1509480552193 : ℚ) / 35220538036283443200

def SurrogateDiagonalTailChunk001Sub001Block077Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27907
    = surrogateDiagTailX0RatChunk001Sub001Block077Part012

theorem surrogateDiagonalTailChunk001Sub001Block077Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part012] using hcert

def TailChunk001Sub001Block077Part013SupportExplicit : Finset ℕ :=
  ([27910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part013 : ℚ :=
  (259511675 : ℚ) / 1292892400054656

def SurrogateDiagonalTailChunk001Sub001Block077Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27910
    = surrogateDiagTailX0RatChunk001Sub001Block077Part013

theorem surrogateDiagonalTailChunk001Sub001Block077Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part013] using hcert

def TailChunk001Sub001Block077Part014SupportExplicit : Finset ℕ :=
  ([27911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part014 : ℚ :=
  (3117385502375 : ℚ) / 71372795625659695104

def SurrogateDiagonalTailChunk001Sub001Block077Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27911
    = surrogateDiagTailX0RatChunk001Sub001Block077Part014

theorem surrogateDiagonalTailChunk001Sub001Block077Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part014] using hcert

def TailChunk001Sub001Block077Part015SupportExplicit : Finset ℕ :=
  ([27913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part015 : ℚ :=
  (95028776609 : ℚ) / 2876819396542342560

def SurrogateDiagonalTailChunk001Sub001Block077Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27913
    = surrogateDiagTailX0RatChunk001Sub001Block077Part015

theorem surrogateDiagonalTailChunk001Sub001Block077Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part015] using hcert

def TailChunk001Sub001Block077Part016SupportExplicit : Finset ℕ :=
  ([27914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part016 : ℚ :=
  (438987256477 : ℚ) / 2963617771369267200

def SurrogateDiagonalTailChunk001Sub001Block077Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27914
    = surrogateDiagTailX0RatChunk001Sub001Block077Part016

theorem surrogateDiagonalTailChunk001Sub001Block077Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part016] using hcert

def TailChunk001Sub001Block077Part017SupportExplicit : Finset ℕ :=
  ([27915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part017 : ℚ :=
  (71359334321 : ℚ) / 612926767433318400

def SurrogateDiagonalTailChunk001Sub001Block077Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27915
    = surrogateDiagTailX0RatChunk001Sub001Block077Part017

theorem surrogateDiagonalTailChunk001Sub001Block077Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part017] using hcert

def TailChunk001Sub001Block077Part018SupportExplicit : Finset ℕ :=
  ([27917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part018 : ℚ :=
  (12177482640625 : ℚ) / 379646697338473327392

def SurrogateDiagonalTailChunk001Sub001Block077Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27917
    = surrogateDiagTailX0RatChunk001Sub001Block077Part018

theorem surrogateDiagonalTailChunk001Sub001Block077Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part018] using hcert

def TailChunk001Sub001Block077Part019SupportExplicit : Finset ℕ :=
  ([27919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part019 : ℚ :=
  (12179227515625 : ℚ) / 379755505906496109522

def SurrogateDiagonalTailChunk001Sub001Block077Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27919
    = surrogateDiagTailX0RatChunk001Sub001Block077Part019

theorem surrogateDiagonalTailChunk001Sub001Block077Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part019] using hcert

def TailChunk001Sub001Block077Part020SupportExplicit : Finset ℕ :=
  ([27921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part020 : ℚ :=
  (411578903489 : ℚ) / 5343804472433049600

def SurrogateDiagonalTailChunk001Sub001Block077Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27921
    = surrogateDiagTailX0RatChunk001Sub001Block077Part020

theorem surrogateDiagonalTailChunk001Sub001Block077Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part020] using hcert

def TailChunk001Sub001Block077Part021SupportExplicit : Finset ℕ :=
  ([27922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part021 : ℚ :=
  (5638802024825 : ℚ) / 39498270815130836544

def SurrogateDiagonalTailChunk001Sub001Block077Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27922
    = surrogateDiagTailX0RatChunk001Sub001Block077Part021

theorem surrogateDiagonalTailChunk001Sub001Block077Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part021] using hcert

def TailChunk001Sub001Block077Part022SupportExplicit : Finset ℕ :=
  ([27923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part022 : ℚ :=
  (3976243464125 : ℚ) / 91077258503523796992

def SurrogateDiagonalTailChunk001Sub001Block077Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27923
    = surrogateDiagTailX0RatChunk001Sub001Block077Part022

theorem surrogateDiagonalTailChunk001Sub001Block077Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part022] using hcert

def TailChunk001Sub001Block077Part023SupportExplicit : Finset ℕ :=
  ([27926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part023 : ℚ :=
  (3046333890625 : ℚ) / 23755129496667366642

def SurrogateDiagonalTailChunk001Sub001Block077Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27926
    = surrogateDiagTailX0RatChunk001Sub001Block077Part023

theorem surrogateDiagonalTailChunk001Sub001Block077Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part023] using hcert

def TailChunk001Sub001Block077Part024SupportExplicit : Finset ℕ :=
  ([27929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block077Part024 : ℚ :=
  (3460965527 : ℚ) / 88298934564461760

def SurrogateDiagonalTailChunk001Sub001Block077Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27929
    = surrogateDiagTailX0RatChunk001Sub001Block077Part024

theorem surrogateDiagonalTailChunk001Sub001Block077Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block077Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block077Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block077Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block077Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block077Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block077HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block077Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block077Part000
    + surrogateDiagTailX0RatChunk001Sub001Block077Part001
    + surrogateDiagTailX0RatChunk001Sub001Block077Part002
    + surrogateDiagTailX0RatChunk001Sub001Block077Part003
    + surrogateDiagTailX0RatChunk001Sub001Block077Part004
    + surrogateDiagTailX0RatChunk001Sub001Block077Part005
    + surrogateDiagTailX0RatChunk001Sub001Block077Part006
    + surrogateDiagTailX0RatChunk001Sub001Block077Part007
    + surrogateDiagTailX0RatChunk001Sub001Block077Part008
    + surrogateDiagTailX0RatChunk001Sub001Block077Part009

def surrogateDiagonalTailChunk001Sub001Block077MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block077Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block077Part010
    + surrogateDiagTailX0RatChunk001Sub001Block077Part011
    + surrogateDiagTailX0RatChunk001Sub001Block077Part012
    + surrogateDiagTailX0RatChunk001Sub001Block077Part013
    + surrogateDiagTailX0RatChunk001Sub001Block077Part014
    + surrogateDiagTailX0RatChunk001Sub001Block077Part015
    + surrogateDiagTailX0RatChunk001Sub001Block077Part016
    + surrogateDiagTailX0RatChunk001Sub001Block077Part017
    + surrogateDiagTailX0RatChunk001Sub001Block077Part018
    + surrogateDiagTailX0RatChunk001Sub001Block077Part019

def surrogateDiagonalTailChunk001Sub001Block077TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block077Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block077Part020
    + surrogateDiagTailX0RatChunk001Sub001Block077Part021
    + surrogateDiagTailX0RatChunk001Sub001Block077Part022
    + surrogateDiagTailX0RatChunk001Sub001Block077Part023
    + surrogateDiagTailX0RatChunk001Sub001Block077Part024

def surrogateDiagonalTailChunk001Sub001Block077Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block077HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block077MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block077TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block077 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block077Part000
    + surrogateDiagTailX0RatChunk001Sub001Block077Part001
    + surrogateDiagTailX0RatChunk001Sub001Block077Part002
    + surrogateDiagTailX0RatChunk001Sub001Block077Part003
    + surrogateDiagTailX0RatChunk001Sub001Block077Part004
    + surrogateDiagTailX0RatChunk001Sub001Block077Part005
    + surrogateDiagTailX0RatChunk001Sub001Block077Part006
    + surrogateDiagTailX0RatChunk001Sub001Block077Part007
    + surrogateDiagTailX0RatChunk001Sub001Block077Part008
    + surrogateDiagTailX0RatChunk001Sub001Block077Part009
    + surrogateDiagTailX0RatChunk001Sub001Block077Part010
    + surrogateDiagTailX0RatChunk001Sub001Block077Part011
    + surrogateDiagTailX0RatChunk001Sub001Block077Part012
    + surrogateDiagTailX0RatChunk001Sub001Block077Part013
    + surrogateDiagTailX0RatChunk001Sub001Block077Part014
    + surrogateDiagTailX0RatChunk001Sub001Block077Part015
    + surrogateDiagTailX0RatChunk001Sub001Block077Part016
    + surrogateDiagTailX0RatChunk001Sub001Block077Part017
    + surrogateDiagTailX0RatChunk001Sub001Block077Part018
    + surrogateDiagTailX0RatChunk001Sub001Block077Part019
    + surrogateDiagTailX0RatChunk001Sub001Block077Part020
    + surrogateDiagTailX0RatChunk001Sub001Block077Part021
    + surrogateDiagTailX0RatChunk001Sub001Block077Part022
    + surrogateDiagTailX0RatChunk001Sub001Block077Part023
    + surrogateDiagTailX0RatChunk001Sub001Block077Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block077_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block077Head + surrogateDiagTailX0RatChunk001Sub001Block077Mid + surrogateDiagTailX0RatChunk001Sub001Block077Tail =
      surrogateDiagTailX0RatChunk001Sub001Block077 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block077Head surrogateDiagTailX0RatChunk001Sub001Block077Mid surrogateDiagTailX0RatChunk001Sub001Block077Tail surrogateDiagTailX0RatChunk001Sub001Block077
  ring

def SurrogateDiagonalTailChunk001Sub001Block077HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block077HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block077Head

def SurrogateDiagonalTailChunk001Sub001Block077MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block077MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block077Mid

def SurrogateDiagonalTailChunk001Sub001Block077TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block077TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block077Tail

theorem surrogateDiagonalTailChunk001Sub001Block077_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block077HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block077MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block077TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block077Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block077 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block077HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block077MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block077TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block077Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block077_eq_head_add_mid_add_tail

/-- Block 078 covers tail-support indices [16950,16975) and q from 27931 to 27970. -/

def TailChunk001Sub001Block078Part000SupportExplicit : Finset ℕ :=
  ([27931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part000 : ℚ :=
  (79234454399 : ℚ) / 1941043099006402560

def SurrogateDiagonalTailChunk001Sub001Block078Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27931
    = surrogateDiagTailX0RatChunk001Sub001Block078Part000

theorem surrogateDiagonalTailChunk001Sub001Block078Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part000] using hcert

def TailChunk001Sub001Block078Part001SupportExplicit : Finset ℕ :=
  ([27933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part001 : ℚ :=
  (866785962757 : ℚ) / 12022798176755587200

def SurrogateDiagonalTailChunk001Sub001Block078Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27933
    = surrogateDiagTailX0RatChunk001Sub001Block078Part001

theorem surrogateDiagonalTailChunk001Sub001Block078Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part001] using hcert

def TailChunk001Sub001Block078Part002SupportExplicit : Finset ℕ :=
  ([27934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part002 : ℚ :=
  (3048079515625 : ℚ) / 23782363806852249042

def SurrogateDiagonalTailChunk001Sub001Block078Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27934
    = surrogateDiagTailX0RatChunk001Sub001Block078Part002

theorem surrogateDiagonalTailChunk001Sub001Block078Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part002] using hcert

def TailChunk001Sub001Block078Part003SupportExplicit : Finset ℕ :=
  ([27935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part003 : ℚ :=
  (587069865737 : ℚ) / 10886088462336000000

def SurrogateDiagonalTailChunk001Sub001Block078Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27935
    = surrogateDiagTailX0RatChunk001Sub001Block078Part003

theorem surrogateDiagonalTailChunk001Sub001Block078Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part003] using hcert

def TailChunk001Sub001Block078Part004SupportExplicit : Finset ℕ :=
  ([27937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part004 : ℚ :=
  (30651461933275 : ℚ) / 589172612411871756288

def SurrogateDiagonalTailChunk001Sub001Block078Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27937
    = surrogateDiagTailX0RatChunk001Sub001Block078Part004

theorem surrogateDiagonalTailChunk001Sub001Block078Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part004] using hcert

def TailChunk001Sub001Block078Part005SupportExplicit : Finset ℕ :=
  ([27938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part005 : ℚ :=
  (471380797831 : ℚ) / 3502928233333555200

def SurrogateDiagonalTailChunk001Sub001Block078Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27938
    = surrogateDiagTailX0RatChunk001Sub001Block078Part005

theorem surrogateDiagonalTailChunk001Sub001Block078Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part005] using hcert

def TailChunk001Sub001Block078Part006SupportExplicit : Finset ℕ :=
  ([27939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part006 : ℚ :=
  (10430024222075 : ℚ) / 137660370362376643584

def SurrogateDiagonalTailChunk001Sub001Block078Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27939
    = surrogateDiagTailX0RatChunk001Sub001Block078Part006

theorem surrogateDiagonalTailChunk001Sub001Block078Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part006] using hcert

def TailChunk001Sub001Block078Part007SupportExplicit : Finset ℕ :=
  ([27941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part007 : ℚ :=
  (19517487025 : ℚ) / 609526311107004192

def SurrogateDiagonalTailChunk001Sub001Block078Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27941
    = surrogateDiagTailX0RatChunk001Sub001Block078Part007

theorem surrogateDiagonalTailChunk001Sub001Block078Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part007] using hcert

def TailChunk001Sub001Block078Part008SupportExplicit : Finset ℕ :=
  ([27942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part008 : ℚ :=
  (5420208534325 : ℚ) / 18801769671169671168

def SurrogateDiagonalTailChunk001Sub001Block078Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27942
    = surrogateDiagTailX0RatChunk001Sub001Block078Part008

theorem surrogateDiagonalTailChunk001Sub001Block078Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part008] using hcert

def TailChunk001Sub001Block078Part009SupportExplicit : Finset ℕ :=
  ([27943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part009 : ℚ :=
  (12200175765625 : ℚ) / 381063033876534656562

def SurrogateDiagonalTailChunk001Sub001Block078Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27943
    = surrogateDiagTailX0RatChunk001Sub001Block078Part009

theorem surrogateDiagonalTailChunk001Sub001Block078Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part009] using hcert

def TailChunk001Sub001Block078Part010SupportExplicit : Finset ℕ :=
  ([27946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part010 : ℚ :=
  (123485121725 : ℚ) / 925091536866951168

def SurrogateDiagonalTailChunk001Sub001Block078Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27946
    = surrogateDiagTailX0RatChunk001Sub001Block078Part010

theorem surrogateDiagonalTailChunk001Sub001Block078Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part010] using hcert

def TailChunk001Sub001Block078Part011SupportExplicit : Finset ℕ :=
  ([27947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part011 : ℚ :=
  (12203668890625 : ℚ) / 381281283031238976882

def SurrogateDiagonalTailChunk001Sub001Block078Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27947
    = surrogateDiagTailX0RatChunk001Sub001Block078Part011

theorem surrogateDiagonalTailChunk001Sub001Block078Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part011] using hcert

def TailChunk001Sub001Block078Part012SupportExplicit : Finset ℕ :=
  ([27949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part012 : ℚ :=
  (1766869639081 : ℚ) / 49028229417002371200

def SurrogateDiagonalTailChunk001Sub001Block078Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27949
    = surrogateDiagTailX0RatChunk001Sub001Block078Part012

theorem surrogateDiagonalTailChunk001Sub001Block078Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part012] using hcert

def TailChunk001Sub001Block078Part013SupportExplicit : Finset ℕ :=
  ([27953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part013 : ℚ :=
  (12208909515625 : ℚ) / 381608832527082135552

def SurrogateDiagonalTailChunk001Sub001Block078Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27953
    = surrogateDiagTailX0RatChunk001Sub001Block078Part013

theorem surrogateDiagonalTailChunk001Sub001Block078Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part013] using hcert

def TailChunk001Sub001Block078Part014SupportExplicit : Finset ℕ :=
  ([27955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part014 : ℚ :=
  (3124935025 : ℚ) / 62504898711086208

def SurrogateDiagonalTailChunk001Sub001Block078Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27955
    = surrogateDiagTailX0RatChunk001Sub001Block078Part014

theorem surrogateDiagonalTailChunk001Sub001Block078Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part014] using hcert

def TailChunk001Sub001Block078Part015SupportExplicit : Finset ℕ :=
  ([27957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part015 : ℚ :=
  (21706905068125 : ℚ) / 301604395121875963008

def SurrogateDiagonalTailChunk001Sub001Block078Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27957
    = surrogateDiagTailX0RatChunk001Sub001Block078Part015

theorem surrogateDiagonalTailChunk001Sub001Block078Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part015] using hcert

def TailChunk001Sub001Block078Part016SupportExplicit : Finset ℕ :=
  ([27958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part016 : ℚ :=
  (9215505105025 : ℚ) / 51436807806449829888

def SurrogateDiagonalTailChunk001Sub001Block078Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27958
    = surrogateDiagTailX0RatChunk001Sub001Block078Part016

theorem surrogateDiagonalTailChunk001Sub001Block078Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part016] using hcert

def TailChunk001Sub001Block078Part017SupportExplicit : Finset ℕ :=
  ([27959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part017 : ℚ :=
  (2963355903175 : ℚ) / 89431458513134635008

def SurrogateDiagonalTailChunk001Sub001Block078Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27959
    = surrogateDiagTailX0RatChunk001Sub001Block078Part017

theorem surrogateDiagonalTailChunk001Sub001Block078Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part017] using hcert

def TailChunk001Sub001Block078Part018SupportExplicit : Finset ℕ :=
  ([27961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part018 : ℚ :=
  (19545438025 : ℚ) / 611273429474406912

def SurrogateDiagonalTailChunk001Sub001Block078Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27961
    = surrogateDiagTailX0RatChunk001Sub001Block078Part018

theorem surrogateDiagonalTailChunk001Sub001Block078Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part018] using hcert

def TailChunk001Sub001Block078Part019SupportExplicit : Finset ℕ :=
  ([27962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part019 : ℚ :=
  (25242216917 : ℚ) / 138267648000000000

def SurrogateDiagonalTailChunk001Sub001Block078Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27962
    = surrogateDiagTailX0RatChunk001Sub001Block078Part019

theorem surrogateDiagonalTailChunk001Sub001Block078Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part019] using hcert

def TailChunk001Sub001Block078Part020SupportExplicit : Finset ℕ :=
  ([27965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part020 : ℚ :=
  (5016139280875 : ℚ) / 60858758936345444352

def SurrogateDiagonalTailChunk001Sub001Block078Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27965
    = surrogateDiagTailX0RatChunk001Sub001Block078Part020

theorem surrogateDiagonalTailChunk001Sub001Block078Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part020] using hcert

def TailChunk001Sub001Block078Part021SupportExplicit : Finset ℕ :=
  ([27966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part021 : ℚ :=
  (22217709925 : ℚ) / 71617864839386112

def SurrogateDiagonalTailChunk001Sub001Block078Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27966
    = surrogateDiagTailX0RatChunk001Sub001Block078Part021

theorem surrogateDiagonalTailChunk001Sub001Block078Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part021] using hcert

def TailChunk001Sub001Block078Part022SupportExplicit : Finset ℕ :=
  ([27967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part022 : ℚ :=
  (12221142015625 : ℚ) / 382373935384733121042

def SurrogateDiagonalTailChunk001Sub001Block078Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27967
    = surrogateDiagTailX0RatChunk001Sub001Block078Part022

theorem surrogateDiagonalTailChunk001Sub001Block078Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part022] using hcert

def TailChunk001Sub001Block078Part023SupportExplicit : Finset ℕ :=
  ([27969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part023 : ℚ :=
  (21725545067725 : ℚ) / 302122615612628638848

def SurrogateDiagonalTailChunk001Sub001Block078Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27969
    = surrogateDiagTailX0RatChunk001Sub001Block078Part023

theorem surrogateDiagonalTailChunk001Sub001Block078Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part023] using hcert

def TailChunk001Sub001Block078Part024SupportExplicit : Finset ℕ :=
  ([27970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block078Part024 : ℚ :=
  (8308249158775 : ℚ) / 39121499486362042368

def SurrogateDiagonalTailChunk001Sub001Block078Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27970
    = surrogateDiagTailX0RatChunk001Sub001Block078Part024

theorem surrogateDiagonalTailChunk001Sub001Block078Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block078Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block078Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block078Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block078Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block078Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block078HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block078Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block078Part000
    + surrogateDiagTailX0RatChunk001Sub001Block078Part001
    + surrogateDiagTailX0RatChunk001Sub001Block078Part002
    + surrogateDiagTailX0RatChunk001Sub001Block078Part003
    + surrogateDiagTailX0RatChunk001Sub001Block078Part004
    + surrogateDiagTailX0RatChunk001Sub001Block078Part005
    + surrogateDiagTailX0RatChunk001Sub001Block078Part006
    + surrogateDiagTailX0RatChunk001Sub001Block078Part007
    + surrogateDiagTailX0RatChunk001Sub001Block078Part008
    + surrogateDiagTailX0RatChunk001Sub001Block078Part009

def surrogateDiagonalTailChunk001Sub001Block078MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block078Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block078Part010
    + surrogateDiagTailX0RatChunk001Sub001Block078Part011
    + surrogateDiagTailX0RatChunk001Sub001Block078Part012
    + surrogateDiagTailX0RatChunk001Sub001Block078Part013
    + surrogateDiagTailX0RatChunk001Sub001Block078Part014
    + surrogateDiagTailX0RatChunk001Sub001Block078Part015
    + surrogateDiagTailX0RatChunk001Sub001Block078Part016
    + surrogateDiagTailX0RatChunk001Sub001Block078Part017
    + surrogateDiagTailX0RatChunk001Sub001Block078Part018
    + surrogateDiagTailX0RatChunk001Sub001Block078Part019

def surrogateDiagonalTailChunk001Sub001Block078TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block078Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block078Part020
    + surrogateDiagTailX0RatChunk001Sub001Block078Part021
    + surrogateDiagTailX0RatChunk001Sub001Block078Part022
    + surrogateDiagTailX0RatChunk001Sub001Block078Part023
    + surrogateDiagTailX0RatChunk001Sub001Block078Part024

def surrogateDiagonalTailChunk001Sub001Block078Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block078HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block078MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block078TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block078 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block078Part000
    + surrogateDiagTailX0RatChunk001Sub001Block078Part001
    + surrogateDiagTailX0RatChunk001Sub001Block078Part002
    + surrogateDiagTailX0RatChunk001Sub001Block078Part003
    + surrogateDiagTailX0RatChunk001Sub001Block078Part004
    + surrogateDiagTailX0RatChunk001Sub001Block078Part005
    + surrogateDiagTailX0RatChunk001Sub001Block078Part006
    + surrogateDiagTailX0RatChunk001Sub001Block078Part007
    + surrogateDiagTailX0RatChunk001Sub001Block078Part008
    + surrogateDiagTailX0RatChunk001Sub001Block078Part009
    + surrogateDiagTailX0RatChunk001Sub001Block078Part010
    + surrogateDiagTailX0RatChunk001Sub001Block078Part011
    + surrogateDiagTailX0RatChunk001Sub001Block078Part012
    + surrogateDiagTailX0RatChunk001Sub001Block078Part013
    + surrogateDiagTailX0RatChunk001Sub001Block078Part014
    + surrogateDiagTailX0RatChunk001Sub001Block078Part015
    + surrogateDiagTailX0RatChunk001Sub001Block078Part016
    + surrogateDiagTailX0RatChunk001Sub001Block078Part017
    + surrogateDiagTailX0RatChunk001Sub001Block078Part018
    + surrogateDiagTailX0RatChunk001Sub001Block078Part019
    + surrogateDiagTailX0RatChunk001Sub001Block078Part020
    + surrogateDiagTailX0RatChunk001Sub001Block078Part021
    + surrogateDiagTailX0RatChunk001Sub001Block078Part022
    + surrogateDiagTailX0RatChunk001Sub001Block078Part023
    + surrogateDiagTailX0RatChunk001Sub001Block078Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block078_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block078Head + surrogateDiagTailX0RatChunk001Sub001Block078Mid + surrogateDiagTailX0RatChunk001Sub001Block078Tail =
      surrogateDiagTailX0RatChunk001Sub001Block078 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block078Head surrogateDiagTailX0RatChunk001Sub001Block078Mid surrogateDiagTailX0RatChunk001Sub001Block078Tail surrogateDiagTailX0RatChunk001Sub001Block078
  ring

def SurrogateDiagonalTailChunk001Sub001Block078HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block078HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block078Head

def SurrogateDiagonalTailChunk001Sub001Block078MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block078MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block078Mid

def SurrogateDiagonalTailChunk001Sub001Block078TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block078TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block078Tail

theorem surrogateDiagonalTailChunk001Sub001Block078_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block078HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block078MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block078TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block078Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block078 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block078HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block078MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block078TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block078Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block078_eq_head_add_mid_add_tail

/-- Block 079 covers tail-support indices [16975,17000) and q from 27971 to 28010. -/

def TailChunk001Sub001Block079Part000SupportExplicit : Finset ℕ :=
  ([27971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part000 : ℚ :=
  (47571368049025 : ℚ) / 1440918369484166135808

def SurrogateDiagonalTailChunk001Sub001Block079Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27971
    = surrogateDiagTailX0RatChunk001Sub001Block079Part000

theorem surrogateDiagonalTailChunk001Sub001Block079Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part000] using hcert

def TailChunk001Sub001Block079Part001SupportExplicit : Finset ℕ :=
  ([27973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part001 : ℚ :=
  (163178480071 : ℚ) / 4176274487049433920

def SurrogateDiagonalTailChunk001Sub001Block079Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27973
    = surrogateDiagTailX0RatChunk001Sub001Block079Part001

theorem surrogateDiagonalTailChunk001Sub001Block079Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part001] using hcert

def TailChunk001Sub001Block079Part002SupportExplicit : Finset ℕ :=
  ([27974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part002 : ℚ :=
  (22562470851 : ℚ) / 168765628445747200

def SurrogateDiagonalTailChunk001Sub001Block079Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27974
    = surrogateDiagTailX0RatChunk001Sub001Block079Part002

theorem surrogateDiagonalTailChunk001Sub001Block079Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part002] using hcert

def TailChunk001Sub001Block079Part003SupportExplicit : Finset ℕ :=
  ([27977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part003 : ℚ :=
  (1908993422281 : ℚ) / 58039435325952000000

def SurrogateDiagonalTailChunk001Sub001Block079Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27977
    = surrogateDiagTailX0RatChunk001Sub001Block079Part003

theorem surrogateDiagonalTailChunk001Sub001Block079Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part003] using hcert

def TailChunk001Sub001Block079Part004SupportExplicit : Finset ℕ :=
  ([27978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part004 : ℚ :=
  (5434185533725 : ℚ) / 18898873508959452288

def SurrogateDiagonalTailChunk001Sub001Block079Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27978
    = surrogateDiagTailX0RatChunk001Sub001Block079Part004

theorem surrogateDiagonalTailChunk001Sub001Block079Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part004] using hcert

def TailChunk001Sub001Block079Part005SupportExplicit : Finset ℕ :=
  ([27982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part005 : ℚ :=
  (11028257401225 : ℚ) / 74815926702828945408

def SurrogateDiagonalTailChunk001Sub001Block079Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27982
    = surrogateDiagTailX0RatChunk001Sub001Block079Part005

theorem surrogateDiagonalTailChunk001Sub001Block079Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part005] using hcert

def TailChunk001Sub001Block079Part006SupportExplicit : Finset ℕ :=
  ([27983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part006 : ℚ :=
  (12235129515625 : ℚ) / 383249746774255975122

def SurrogateDiagonalTailChunk001Sub001Block079Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27983
    = surrogateDiagTailX0RatChunk001Sub001Block079Part006

theorem surrogateDiagonalTailChunk001Sub001Block079Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part006] using hcert

def TailChunk001Sub001Block079Part007SupportExplicit : Finset ℕ :=
  ([27985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part007 : ℚ :=
  (3641308806875 : ℚ) / 66836527408025174016

def SurrogateDiagonalTailChunk001Sub001Block079Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27985
    = surrogateDiagTailX0RatChunk001Sub001Block079Part007

theorem surrogateDiagonalTailChunk001Sub001Block079Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part007] using hcert

def TailChunk001Sub001Block079Part008SupportExplicit : Finset ℕ :=
  ([27986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part008 : ℚ :=
  (9233978551225 : ℚ) / 51643277422858378368

def SurrogateDiagonalTailChunk001Sub001Block079Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27986
    = surrogateDiagTailX0RatChunk001Sub001Block079Part008

theorem surrogateDiagonalTailChunk001Sub001Block079Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part008] using hcert

def TailChunk001Sub001Block079Part009SupportExplicit : Finset ℕ :=
  ([27987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part009 : ℚ :=
  (196837381639 : ℚ) / 2421147131703820800

def SurrogateDiagonalTailChunk001Sub001Block079Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27987
    = surrogateDiagTailX0RatChunk001Sub001Block079Part009

theorem surrogateDiagonalTailChunk001Sub001Block079Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part009] using hcert

def TailChunk001Sub001Block079Part010SupportExplicit : Finset ℕ :=
  ([27989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part010 : ℚ :=
  (13991503458125 : ℚ) / 370680428453778948096

def SurrogateDiagonalTailChunk001Sub001Block079Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27989
    = surrogateDiagTailX0RatChunk001Sub001Block079Part010

theorem surrogateDiagonalTailChunk001Sub001Block079Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part010] using hcert

def TailChunk001Sub001Block079Part011SupportExplicit : Finset ℕ :=
  ([27991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part011 : ℚ :=
  (7502623050225 : ℚ) / 213452198134748807168

def SurrogateDiagonalTailChunk001Sub001Block079Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27991
    = surrogateDiagTailX0RatChunk001Sub001Block079Part011

theorem surrogateDiagonalTailChunk001Sub001Block079Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part011] using hcert

def TailChunk001Sub001Block079Part012SupportExplicit : Finset ℕ :=
  ([27993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part012 : ℚ :=
  (1212060839 : ℚ) / 10756172180275200

def SurrogateDiagonalTailChunk001Sub001Block079Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27993
    = surrogateDiagTailX0RatChunk001Sub001Block079Part012

theorem surrogateDiagonalTailChunk001Sub001Block079Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part012] using hcert

def TailChunk001Sub001Block079Part013SupportExplicit : Finset ℕ :=
  ([27994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part013 : ℚ :=
  (3061187640625 : ℚ) / 23987368272111712032

def SurrogateDiagonalTailChunk001Sub001Block079Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27994
    = surrogateDiagTailX0RatChunk001Sub001Block079Part013

theorem surrogateDiagonalTailChunk001Sub001Block079Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part013] using hcert

def TailChunk001Sub001Block079Part014SupportExplicit : Finset ℕ :=
  ([27995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part014 : ℚ :=
  (524097518627 : ℚ) / 8526124480207257600

def SurrogateDiagonalTailChunk001Sub001Block079Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27995
    = surrogateDiagTailX0RatChunk001Sub001Block079Part014

theorem surrogateDiagonalTailChunk001Sub001Block079Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part014] using hcert

def TailChunk001Sub001Block079Part015SupportExplicit : Finset ℕ :=
  ([27997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part015 : ℚ :=
  (12247375140625 : ℚ) / 384017315140927264032

def SurrogateDiagonalTailChunk001Sub001Block079Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27997
    = surrogateDiagTailX0RatChunk001Sub001Block079Part015

theorem surrogateDiagonalTailChunk001Sub001Block079Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part015] using hcert

def TailChunk001Sub001Block079Part016SupportExplicit : Finset ℕ :=
  ([27998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part016 : ℚ :=
  (3062062515625 : ℚ) / 24001082196307954002

def SurrogateDiagonalTailChunk001Sub001Block079Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 27998
    = surrogateDiagTailX0RatChunk001Sub001Block079Part016

theorem surrogateDiagonalTailChunk001Sub001Block079Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part016] using hcert

def TailChunk001Sub001Block079Part017SupportExplicit : Finset ℕ :=
  ([28001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part017 : ℚ :=
  (784056001 : ℚ) / 24591157248000000

def SurrogateDiagonalTailChunk001Sub001Block079Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28001
    = surrogateDiagTailX0RatChunk001Sub001Block079Part017

theorem surrogateDiagonalTailChunk001Sub001Block079Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part017] using hcert

def TailChunk001Sub001Block079Part018SupportExplicit : Finset ℕ :=
  ([28002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part018 : ℚ :=
  (1599094467575 : ℚ) / 4542371785224585216

def SurrogateDiagonalTailChunk001Sub001Block079Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28002
    = surrogateDiagTailX0RatChunk001Sub001Block079Part018

theorem surrogateDiagonalTailChunk001Sub001Block079Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part018] using hcert

def TailChunk001Sub001Block079Part019SupportExplicit : Finset ℕ :=
  ([28003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part019 : ℚ :=
  (21228102601 : ℚ) / 629479573652582400

def SurrogateDiagonalTailChunk001Sub001Block079Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28003
    = surrogateDiagTailX0RatChunk001Sub001Block079Part019

theorem surrogateDiagonalTailChunk001Sub001Block079Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part019] using hcert

def TailChunk001Sub001Block079Part020SupportExplicit : Finset ℕ :=
  ([28005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part020 : ℚ :=
  (3591018958225 : ℚ) / 31043692517000159232

def SurrogateDiagonalTailChunk001Sub001Block079Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28005
    = surrogateDiagTailX0RatChunk001Sub001Block079Part020

theorem surrogateDiagonalTailChunk001Sub001Block079Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part020] using hcert

def TailChunk001Sub001Block079Part021SupportExplicit : Finset ℕ :=
  ([28006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part021 : ℚ :=
  (372870125467 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub001Block079Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28006
    = surrogateDiagTailX0RatChunk001Sub001Block079Part021

theorem surrogateDiagonalTailChunk001Sub001Block079Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part021] using hcert

def TailChunk001Sub001Block079Part022SupportExplicit : Finset ℕ :=
  ([28007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part022 : ℚ :=
  (296034147989 : ℚ) / 6636847104000000000

def SurrogateDiagonalTailChunk001Sub001Block079Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28007
    = surrogateDiagTailX0RatChunk001Sub001Block079Part022

theorem surrogateDiagonalTailChunk001Sub001Block079Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part022] using hcert

def TailChunk001Sub001Block079Part023SupportExplicit : Finset ℕ :=
  ([28009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part023 : ℚ :=
  (287177490875 : ℚ) / 8468549480974270464

def SurrogateDiagonalTailChunk001Sub001Block079Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28009
    = surrogateDiagTailX0RatChunk001Sub001Block079Part023

theorem surrogateDiagonalTailChunk001Sub001Block079Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part023] using hcert

def TailChunk001Sub001Block079Part024SupportExplicit : Finset ℕ :=
  ([28010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block079Part024 : ℚ :=
  (333281375899 : ℚ) / 1573834063872000000

def SurrogateDiagonalTailChunk001Sub001Block079Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 28010
    = surrogateDiagTailX0RatChunk001Sub001Block079Part024

theorem surrogateDiagonalTailChunk001Sub001Block079Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block079Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block079Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block079Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block079Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block079Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block079HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block079Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block079Part000
    + surrogateDiagTailX0RatChunk001Sub001Block079Part001
    + surrogateDiagTailX0RatChunk001Sub001Block079Part002
    + surrogateDiagTailX0RatChunk001Sub001Block079Part003
    + surrogateDiagTailX0RatChunk001Sub001Block079Part004
    + surrogateDiagTailX0RatChunk001Sub001Block079Part005
    + surrogateDiagTailX0RatChunk001Sub001Block079Part006
    + surrogateDiagTailX0RatChunk001Sub001Block079Part007
    + surrogateDiagTailX0RatChunk001Sub001Block079Part008
    + surrogateDiagTailX0RatChunk001Sub001Block079Part009

def surrogateDiagonalTailChunk001Sub001Block079MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block079Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block079Part010
    + surrogateDiagTailX0RatChunk001Sub001Block079Part011
    + surrogateDiagTailX0RatChunk001Sub001Block079Part012
    + surrogateDiagTailX0RatChunk001Sub001Block079Part013
    + surrogateDiagTailX0RatChunk001Sub001Block079Part014
    + surrogateDiagTailX0RatChunk001Sub001Block079Part015
    + surrogateDiagTailX0RatChunk001Sub001Block079Part016
    + surrogateDiagTailX0RatChunk001Sub001Block079Part017
    + surrogateDiagTailX0RatChunk001Sub001Block079Part018
    + surrogateDiagTailX0RatChunk001Sub001Block079Part019

def surrogateDiagonalTailChunk001Sub001Block079TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block079Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block079Part020
    + surrogateDiagTailX0RatChunk001Sub001Block079Part021
    + surrogateDiagTailX0RatChunk001Sub001Block079Part022
    + surrogateDiagTailX0RatChunk001Sub001Block079Part023
    + surrogateDiagTailX0RatChunk001Sub001Block079Part024

def surrogateDiagonalTailChunk001Sub001Block079Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block079HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block079MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block079TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block079 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block079Part000
    + surrogateDiagTailX0RatChunk001Sub001Block079Part001
    + surrogateDiagTailX0RatChunk001Sub001Block079Part002
    + surrogateDiagTailX0RatChunk001Sub001Block079Part003
    + surrogateDiagTailX0RatChunk001Sub001Block079Part004
    + surrogateDiagTailX0RatChunk001Sub001Block079Part005
    + surrogateDiagTailX0RatChunk001Sub001Block079Part006
    + surrogateDiagTailX0RatChunk001Sub001Block079Part007
    + surrogateDiagTailX0RatChunk001Sub001Block079Part008
    + surrogateDiagTailX0RatChunk001Sub001Block079Part009
    + surrogateDiagTailX0RatChunk001Sub001Block079Part010
    + surrogateDiagTailX0RatChunk001Sub001Block079Part011
    + surrogateDiagTailX0RatChunk001Sub001Block079Part012
    + surrogateDiagTailX0RatChunk001Sub001Block079Part013
    + surrogateDiagTailX0RatChunk001Sub001Block079Part014
    + surrogateDiagTailX0RatChunk001Sub001Block079Part015
    + surrogateDiagTailX0RatChunk001Sub001Block079Part016
    + surrogateDiagTailX0RatChunk001Sub001Block079Part017
    + surrogateDiagTailX0RatChunk001Sub001Block079Part018
    + surrogateDiagTailX0RatChunk001Sub001Block079Part019
    + surrogateDiagTailX0RatChunk001Sub001Block079Part020
    + surrogateDiagTailX0RatChunk001Sub001Block079Part021
    + surrogateDiagTailX0RatChunk001Sub001Block079Part022
    + surrogateDiagTailX0RatChunk001Sub001Block079Part023
    + surrogateDiagTailX0RatChunk001Sub001Block079Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block079_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block079Head + surrogateDiagTailX0RatChunk001Sub001Block079Mid + surrogateDiagTailX0RatChunk001Sub001Block079Tail =
      surrogateDiagTailX0RatChunk001Sub001Block079 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block079Head surrogateDiagTailX0RatChunk001Sub001Block079Mid surrogateDiagTailX0RatChunk001Sub001Block079Tail surrogateDiagTailX0RatChunk001Sub001Block079
  ring

def SurrogateDiagonalTailChunk001Sub001Block079HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block079HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block079Head

def SurrogateDiagonalTailChunk001Sub001Block079MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block079MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block079Mid

def SurrogateDiagonalTailChunk001Sub001Block079TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block079TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block079Tail

theorem surrogateDiagonalTailChunk001Sub001Block079_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block079HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block079MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block079TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block079Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block079 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block079HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block079MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block079TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block079Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block079_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
