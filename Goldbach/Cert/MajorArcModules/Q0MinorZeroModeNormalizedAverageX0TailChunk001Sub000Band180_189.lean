import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [180,190). -/

/-- Block 180 covers tail-support indices [14500,14525) and q from 23901 to 23938. -/

def TailChunk001Sub000Block180Part000SupportExplicit : Finset ℕ :=
  ([23901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part000 : ℚ :=
  (595961206717 : ℚ) / 5567390871139123200

def SurrogateDiagonalTailChunk001Sub000Block180Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23901
    = surrogateDiagTailX0RatChunk001Sub000Block180Part000

theorem surrogateDiagonalTailChunk001Sub000Block180Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part000] using hcert

def TailChunk001Sub000Block180Part001SupportExplicit : Finset ℕ :=
  ([23902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part001 : ℚ :=
  (2372990276225 : ℚ) / 9631314361813303296

def SurrogateDiagonalTailChunk001Sub000Block180Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23902
    = surrogateDiagTailX0RatChunk001Sub000Block180Part001

theorem surrogateDiagonalTailChunk001Sub000Block180Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part001] using hcert

def TailChunk001Sub000Block180Part002SupportExplicit : Finset ℕ :=
  ([23903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part002 : ℚ :=
  (220598216129 : ℚ) / 3744296101478400000

def SurrogateDiagonalTailChunk001Sub000Block180Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23903
    = surrogateDiagTailX0RatChunk001Sub000Block180Part002

theorem surrogateDiagonalTailChunk001Sub000Block180Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part002] using hcert

def TailChunk001Sub000Block180Part003SupportExplicit : Finset ℕ :=
  ([23905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part003 : ℚ :=
  (1880499221525 : ℚ) / 19941912893313810432

def SurrogateDiagonalTailChunk001Sub000Block180Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23905
    = surrogateDiagTailX0RatChunk001Sub000Block180Part003

theorem surrogateDiagonalTailChunk001Sub000Block180Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part003] using hcert

def TailChunk001Sub000Block180Part004SupportExplicit : Finset ℕ :=
  ([23906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part004 : ℚ :=
  (2232409515625 : ℚ) / 12756431621726871552

def SurrogateDiagonalTailChunk001Sub000Block180Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23906
    = surrogateDiagTailX0RatChunk001Sub000Block180Part004

theorem surrogateDiagonalTailChunk001Sub000Block180Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part004] using hcert

def TailChunk001Sub000Block180Part005SupportExplicit : Finset ℕ :=
  ([23907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part005 : ℚ :=
  (862198790275 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk001Sub000Block180Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23907
    = surrogateDiagTailX0RatChunk001Sub000Block180Part005

theorem surrogateDiagonalTailChunk001Sub000Block180Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part005] using hcert

def TailChunk001Sub000Block180Part006SupportExplicit : Finset ℕ :=
  ([23909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part006 : ℚ :=
  (8931879390625 : ℚ) / 204239555306607258912

def SurrogateDiagonalTailChunk001Sub000Block180Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23909
    = surrogateDiagTailX0RatChunk001Sub000Block180Part006

theorem surrogateDiagonalTailChunk001Sub000Block180Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part006] using hcert

def TailChunk001Sub000Block180Part007SupportExplicit : Finset ℕ :=
  ([23910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part007 : ℚ :=
  (951180791175 : ℚ) / 1370622393354551296

def SurrogateDiagonalTailChunk001Sub000Block180Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23910
    = surrogateDiagTailX0RatChunk001Sub000Block180Part007

theorem surrogateDiagonalTailChunk001Sub000Block180Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part007] using hcert

def TailChunk001Sub000Block180Part008SupportExplicit : Finset ℕ :=
  ([23911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part008 : ℚ :=
  (14293398025 : ℚ) / 326892649138346322

def SurrogateDiagonalTailChunk001Sub000Block180Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23911
    = surrogateDiagTailX0RatChunk001Sub000Block180Part008

theorem surrogateDiagonalTailChunk001Sub000Block180Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part008] using hcert

def TailChunk001Sub000Block180Part009SupportExplicit : Finset ℕ :=
  ([23914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part009 : ℚ :=
  (306807926401 : ℚ) / 1391253119800963200

def SurrogateDiagonalTailChunk001Sub000Block180Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23914
    = surrogateDiagTailX0RatChunk001Sub000Block180Part009

theorem surrogateDiagonalTailChunk001Sub000Block180Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part009] using hcert

def TailChunk001Sub000Block180Part010SupportExplicit : Finset ℕ :=
  ([23915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part010 : ℚ :=
  (476432796875 : ℚ) / 6973709848284721536

def SurrogateDiagonalTailChunk001Sub000Block180Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23915
    = surrogateDiagTailX0RatChunk001Sub000Block180Part010

theorem surrogateDiagonalTailChunk001Sub000Block180Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part010] using hcert

def TailChunk001Sub000Block180Part011SupportExplicit : Finset ℕ :=
  ([23917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part011 : ℚ :=
  (8937857640625 : ℚ) / 204513059861962735392

def SurrogateDiagonalTailChunk001Sub000Block180Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23917
    = surrogateDiagTailX0RatChunk001Sub000Block180Part011

theorem surrogateDiagonalTailChunk001Sub000Block180Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part011] using hcert

def TailChunk001Sub000Block180Part012SupportExplicit : Finset ℕ :=
  ([23918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part012 : ℚ :=
  (2234651265625 : ℚ) / 12782066241372670962

def SurrogateDiagonalTailChunk001Sub000Block180Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23918
    = surrogateDiagTailX0RatChunk001Sub000Block180Part012

theorem surrogateDiagonalTailChunk001Sub000Block180Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part012] using hcert

def TailChunk001Sub000Block180Part013SupportExplicit : Finset ℕ :=
  ([23919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part013 : ℚ :=
  (3517302805825 : ℚ) / 21492466631810482176

def SurrogateDiagonalTailChunk001Sub000Block180Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23919
    = surrogateDiagTailX0RatChunk001Sub000Block180Part013

theorem surrogateDiagonalTailChunk001Sub000Block180Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part013] using hcert

def TailChunk001Sub000Block180Part014SupportExplicit : Finset ℕ :=
  ([23921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part014 : ℚ :=
  (32351263109125 : ℚ) / 657414749829988510848

def SurrogateDiagonalTailChunk001Sub000Block180Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23921
    = surrogateDiagTailX0RatChunk001Sub000Block180Part014

theorem surrogateDiagonalTailChunk001Sub000Block180Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part014] using hcert

def TailChunk001Sub000Block180Part015SupportExplicit : Finset ℕ :=
  ([23923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part015 : ℚ :=
  (11430243938175 : ℚ) / 248537416736008247296

def SurrogateDiagonalTailChunk001Sub000Block180Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23923
    = surrogateDiagTailX0RatChunk001Sub000Block180Part015

theorem surrogateDiagonalTailChunk001Sub000Block180Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part015] using hcert

def TailChunk001Sub000Block180Part016SupportExplicit : Finset ℕ :=
  ([23926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part016 : ℚ :=
  (247541981725 : ℚ) / 984975196935937536

def SurrogateDiagonalTailChunk001Sub000Block180Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23926
    = surrogateDiagTailX0RatChunk001Sub000Block180Part016

theorem surrogateDiagonalTailChunk001Sub000Block180Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part016] using hcert

def TailChunk001Sub000Block180Part017SupportExplicit : Finset ℕ :=
  ([23927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part017 : ℚ :=
  (1376868847 : ℚ) / 30365160969830400

def SurrogateDiagonalTailChunk001Sub000Block180Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23927
    = surrogateDiagTailX0RatChunk001Sub000Block180Part017

theorem surrogateDiagonalTailChunk001Sub000Block180Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part017] using hcert

def TailChunk001Sub000Block180Part018SupportExplicit : Finset ℕ :=
  ([23929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part018 : ℚ :=
  (8946828765625 : ℚ) / 204923831632928543232

def SurrogateDiagonalTailChunk001Sub000Block180Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23929
    = surrogateDiagTailX0RatChunk001Sub000Block180Part018

theorem surrogateDiagonalTailChunk001Sub000Block180Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part018] using hcert

def TailChunk001Sub000Block180Part019SupportExplicit : Finset ℕ :=
  ([23930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part019 : ℚ :=
  (2146374551775 : ℚ) / 6985383768892112896

def SurrogateDiagonalTailChunk001Sub000Block180Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23930
    = surrogateDiagTailX0RatChunk001Sub000Block180Part019

theorem surrogateDiagonalTailChunk001Sub000Block180Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part019] using hcert

def TailChunk001Sub000Block180Part020SupportExplicit : Finset ℕ :=
  ([23933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part020 : ℚ :=
  (2829990517175 : ℚ) / 39579656693295845376

def SurrogateDiagonalTailChunk001Sub000Block180Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23933
    = surrogateDiagTailX0RatChunk001Sub000Block180Part020

theorem surrogateDiagonalTailChunk001Sub000Block180Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part020] using hcert

def TailChunk001Sub000Block180Part021SupportExplicit : Finset ℕ :=
  ([23934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part021 : ℚ :=
  (3976660601125 : ℚ) / 10119695389280421888

def SurrogateDiagonalTailChunk001Sub000Block180Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23934
    = surrogateDiagTailX0RatChunk001Sub000Block180Part021

theorem surrogateDiagonalTailChunk001Sub000Block180Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part021] using hcert

def TailChunk001Sub000Block180Part022SupportExplicit : Finset ℕ :=
  ([23935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part022 : ℚ :=
  (1431690390625 : ℚ) / 20991217019667788928

def SurrogateDiagonalTailChunk001Sub000Block180Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23935
    = surrogateDiagTailX0RatChunk001Sub000Block180Part022

theorem surrogateDiagonalTailChunk001Sub000Block180Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part022] using hcert

def TailChunk001Sub000Block180Part023SupportExplicit : Finset ℕ :=
  ([23937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part023 : ℚ :=
  (122524405643 : ℚ) / 1184718688358400000

def SurrogateDiagonalTailChunk001Sub000Block180Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23937
    = surrogateDiagTailX0RatChunk001Sub000Block180Part023

theorem surrogateDiagonalTailChunk001Sub000Block180Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part023] using hcert

def TailChunk001Sub000Block180Part024SupportExplicit : Finset ℕ :=
  ([23938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block180Part024 : ℚ :=
  (2238390015625 : ℚ) / 12824876440010883072

def SurrogateDiagonalTailChunk001Sub000Block180Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23938
    = surrogateDiagTailX0RatChunk001Sub000Block180Part024

theorem surrogateDiagonalTailChunk001Sub000Block180Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block180Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block180Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block180Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block180Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block180Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block180Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block180HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block180Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block180Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block180Part000
    + surrogateDiagTailX0RatChunk001Sub000Block180Part001
    + surrogateDiagTailX0RatChunk001Sub000Block180Part002
    + surrogateDiagTailX0RatChunk001Sub000Block180Part003
    + surrogateDiagTailX0RatChunk001Sub000Block180Part004
    + surrogateDiagTailX0RatChunk001Sub000Block180Part005
    + surrogateDiagTailX0RatChunk001Sub000Block180Part006
    + surrogateDiagTailX0RatChunk001Sub000Block180Part007
    + surrogateDiagTailX0RatChunk001Sub000Block180Part008
    + surrogateDiagTailX0RatChunk001Sub000Block180Part009

def surrogateDiagonalTailChunk001Sub000Block180MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block180Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block180Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block180Part010
    + surrogateDiagTailX0RatChunk001Sub000Block180Part011
    + surrogateDiagTailX0RatChunk001Sub000Block180Part012
    + surrogateDiagTailX0RatChunk001Sub000Block180Part013
    + surrogateDiagTailX0RatChunk001Sub000Block180Part014
    + surrogateDiagTailX0RatChunk001Sub000Block180Part015
    + surrogateDiagTailX0RatChunk001Sub000Block180Part016
    + surrogateDiagTailX0RatChunk001Sub000Block180Part017
    + surrogateDiagTailX0RatChunk001Sub000Block180Part018
    + surrogateDiagTailX0RatChunk001Sub000Block180Part019

def surrogateDiagonalTailChunk001Sub000Block180TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block180Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block180Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block180Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block180Part020
    + surrogateDiagTailX0RatChunk001Sub000Block180Part021
    + surrogateDiagTailX0RatChunk001Sub000Block180Part022
    + surrogateDiagTailX0RatChunk001Sub000Block180Part023
    + surrogateDiagTailX0RatChunk001Sub000Block180Part024

def surrogateDiagonalTailChunk001Sub000Block180Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block180HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block180MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block180TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block180 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block180Part000
    + surrogateDiagTailX0RatChunk001Sub000Block180Part001
    + surrogateDiagTailX0RatChunk001Sub000Block180Part002
    + surrogateDiagTailX0RatChunk001Sub000Block180Part003
    + surrogateDiagTailX0RatChunk001Sub000Block180Part004
    + surrogateDiagTailX0RatChunk001Sub000Block180Part005
    + surrogateDiagTailX0RatChunk001Sub000Block180Part006
    + surrogateDiagTailX0RatChunk001Sub000Block180Part007
    + surrogateDiagTailX0RatChunk001Sub000Block180Part008
    + surrogateDiagTailX0RatChunk001Sub000Block180Part009
    + surrogateDiagTailX0RatChunk001Sub000Block180Part010
    + surrogateDiagTailX0RatChunk001Sub000Block180Part011
    + surrogateDiagTailX0RatChunk001Sub000Block180Part012
    + surrogateDiagTailX0RatChunk001Sub000Block180Part013
    + surrogateDiagTailX0RatChunk001Sub000Block180Part014
    + surrogateDiagTailX0RatChunk001Sub000Block180Part015
    + surrogateDiagTailX0RatChunk001Sub000Block180Part016
    + surrogateDiagTailX0RatChunk001Sub000Block180Part017
    + surrogateDiagTailX0RatChunk001Sub000Block180Part018
    + surrogateDiagTailX0RatChunk001Sub000Block180Part019
    + surrogateDiagTailX0RatChunk001Sub000Block180Part020
    + surrogateDiagTailX0RatChunk001Sub000Block180Part021
    + surrogateDiagTailX0RatChunk001Sub000Block180Part022
    + surrogateDiagTailX0RatChunk001Sub000Block180Part023
    + surrogateDiagTailX0RatChunk001Sub000Block180Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block180_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block180Head + surrogateDiagTailX0RatChunk001Sub000Block180Mid + surrogateDiagTailX0RatChunk001Sub000Block180Tail =
      surrogateDiagTailX0RatChunk001Sub000Block180 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block180Head surrogateDiagTailX0RatChunk001Sub000Block180Mid surrogateDiagTailX0RatChunk001Sub000Block180Tail surrogateDiagTailX0RatChunk001Sub000Block180
  ring

def SurrogateDiagonalTailChunk001Sub000Block180HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block180HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block180Head

def SurrogateDiagonalTailChunk001Sub000Block180MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block180MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block180Mid

def SurrogateDiagonalTailChunk001Sub000Block180TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block180TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block180Tail

theorem surrogateDiagonalTailChunk001Sub000Block180_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block180HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block180MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block180TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block180Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block180 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block180HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block180MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block180TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block180Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block180_eq_head_add_mid_add_tail

/-- Block 181 covers tail-support indices [14525,14550) and q from 23939 to 23979. -/

def TailChunk001Sub000Block181Part000SupportExplicit : Finset ℕ :=
  ([23939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part000 : ℚ :=
  (1999925015375 : ℚ) / 43024716025919391744

def SurrogateDiagonalTailChunk001Sub000Block181Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23939
    = surrogateDiagTailX0RatChunk001Sub000Block181Part000

theorem surrogateDiagonalTailChunk001Sub000Block181Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part000] using hcert

def TailChunk001Sub000Block181Part001SupportExplicit : Finset ℕ :=
  ([23941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part001 : ℚ :=
  (34873605798925 : ℚ) / 773564842832067821568

def SurrogateDiagonalTailChunk001Sub000Block181Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23941
    = surrogateDiagTailX0RatChunk001Sub000Block181Part001

theorem surrogateDiagonalTailChunk001Sub000Block181Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part001] using hcert

def TailChunk001Sub000Block181Part002SupportExplicit : Finset ℕ :=
  ([23942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part002 : ℚ :=
  (3582621025 : ℚ) / 20533522188070962

def SurrogateDiagonalTailChunk001Sub000Block181Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23942
    = surrogateDiagTailX0RatChunk001Sub000Block181Part002

theorem surrogateDiagonalTailChunk001Sub000Block181Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part002] using hcert

def TailChunk001Sub000Block181Part003SupportExplicit : Finset ℕ :=
  ([23943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part003 : ℚ :=
  (14693492934325 : ℚ) / 134320394914918975488

def SurrogateDiagonalTailChunk001Sub000Block181Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23943
    = surrogateDiagTailX0RatChunk001Sub000Block181Part003

theorem surrogateDiagonalTailChunk001Sub000Block181Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part003] using hcert

def TailChunk001Sub000Block181Part004SupportExplicit : Finset ℕ :=
  ([23945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part004 : ℚ :=
  (477629046875 : ℚ) / 7008775573528221696

def SurrogateDiagonalTailChunk001Sub000Block181Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23945
    = surrogateDiagTailX0RatChunk001Sub000Block181Part004

theorem surrogateDiagonalTailChunk001Sub000Block181Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part004] using hcert

def TailChunk001Sub000Block181Part005SupportExplicit : Finset ℕ :=
  ([23946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part005 : ℚ :=
  (3553953482725 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk001Sub000Block181Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23946
    = surrogateDiagTailX0RatChunk001Sub000Block181Part005

theorem surrogateDiagonalTailChunk001Sub000Block181Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part005] using hcert

def TailChunk001Sub000Block181Part006SupportExplicit : Finset ℕ :=
  ([23947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part006 : ℚ :=
  (877606002793 : ℚ) / 11971225926432000000

def SurrogateDiagonalTailChunk001Sub000Block181Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23947
    = surrogateDiagTailX0RatChunk001Sub000Block181Part006

theorem surrogateDiagonalTailChunk001Sub000Block181Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part006] using hcert

def TailChunk001Sub000Block181Part007SupportExplicit : Finset ℕ :=
  ([23951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part007 : ℚ :=
  (17126143412675 : ℚ) / 371786136302960354304

def SurrogateDiagonalTailChunk001Sub000Block181Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23951
    = surrogateDiagTailX0RatChunk001Sub000Block181Part007

theorem surrogateDiagonalTailChunk001Sub000Block181Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part007] using hcert

def TailChunk001Sub000Block181Part008SupportExplicit : Finset ℕ :=
  ([23953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part008 : ℚ :=
  (2006146371475 : ℚ) / 40252923330542174208

def SurrogateDiagonalTailChunk001Sub000Block181Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23953
    = surrogateDiagTailX0RatChunk001Sub000Block181Part008

theorem surrogateDiagonalTailChunk001Sub000Block181Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part008] using hcert

def TailChunk001Sub000Block181Part009SupportExplicit : Finset ℕ :=
  ([23954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part009 : ℚ :=
  (3206064869675 : ℚ) / 11270572171610701824

def SurrogateDiagonalTailChunk001Sub000Block181Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23954
    = surrogateDiagTailX0RatChunk001Sub000Block181Part009

theorem surrogateDiagonalTailChunk001Sub000Block181Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part009] using hcert

def TailChunk001Sub000Block181Part010SupportExplicit : Finset ℕ :=
  ([23955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part010 : ℚ :=
  (1313583993425 : ℚ) / 8306696976033447936

def SurrogateDiagonalTailChunk001Sub000Block181Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23955
    = surrogateDiagTailX0RatChunk001Sub000Block181Part010

theorem surrogateDiagonalTailChunk001Sub000Block181Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part010] using hcert

def TailChunk001Sub000Block181Part011SupportExplicit : Finset ℕ :=
  ([23957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part011 : ℚ :=
  (8967778890625 : ℚ) / 205884705358632820512

def SurrogateDiagonalTailChunk001Sub000Block181Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23957
    = surrogateDiagTailX0RatChunk001Sub000Block181Part011

theorem surrogateDiagonalTailChunk001Sub000Block181Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part011] using hcert

def TailChunk001Sub000Block181Part012SupportExplicit : Finset ℕ :=
  ([23959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part012 : ℚ :=
  (27587487972925 : ℚ) / 462303089367038558208

def SurrogateDiagonalTailChunk001Sub000Block181Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23959
    = surrogateDiagTailX0RatChunk001Sub000Block181Part012

theorem surrogateDiagonalTailChunk001Sub000Block181Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part012] using hcert

def TailChunk001Sub000Block181Part013SupportExplicit : Finset ℕ :=
  ([23962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part013 : ℚ :=
  (3588609025 : ℚ) / 20602224837203232

def SurrogateDiagonalTailChunk001Sub000Block181Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23962
    = surrogateDiagTailX0RatChunk001Sub000Block181Part013

theorem surrogateDiagonalTailChunk001Sub000Block181Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part013] using hcert

def TailChunk001Sub000Block181Part014SupportExplicit : Finset ℕ :=
  ([23963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part014 : ℚ :=
  (1350373626247 : ℚ) / 28776705378973747200

def SurrogateDiagonalTailChunk001Sub000Block181Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23963
    = surrogateDiagTailX0RatChunk001Sub000Block181Part014

theorem surrogateDiagonalTailChunk001Sub000Block181Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part014] using hcert

def TailChunk001Sub000Block181Part015SupportExplicit : Finset ℕ :=
  ([23965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part015 : ℚ :=
  (1435282140625 : ℚ) / 21096678233296109568

def SurrogateDiagonalTailChunk001Sub000Block181Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23965
    = surrogateDiagTailX0RatChunk001Sub000Block181Part015

theorem surrogateDiagonalTailChunk001Sub000Block181Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part015] using hcert

def TailChunk001Sub000Block181Part016SupportExplicit : Finset ℕ :=
  ([23966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part016 : ℚ :=
  (22239000081 : ℚ) / 114208831711969280

def SurrogateDiagonalTailChunk001Sub000Block181Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23966
    = surrogateDiagTailX0RatChunk001Sub000Block181Part016

theorem surrogateDiagonalTailChunk001Sub000Block181Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part016] using hcert

def TailChunk001Sub000Block181Part017SupportExplicit : Finset ℕ :=
  ([23969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part017 : ℚ :=
  (119795243629 : ℚ) / 2250703839943437120

def SurrogateDiagonalTailChunk001Sub000Block181Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23969
    = surrogateDiagTailX0RatChunk001Sub000Block181Part017

theorem surrogateDiagonalTailChunk001Sub000Block181Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part017] using hcert

def TailChunk001Sub000Block181Part018SupportExplicit : Finset ℕ :=
  ([23970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part018 : ℚ :=
  (1305873805925 : ℚ) / 1502685405835689984

def SurrogateDiagonalTailChunk001Sub000Block181Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23970
    = surrogateDiagTailX0RatChunk001Sub000Block181Part018

theorem surrogateDiagonalTailChunk001Sub000Block181Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part018] using hcert

def TailChunk001Sub000Block181Part019SupportExplicit : Finset ℕ :=
  ([23971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part019 : ℚ :=
  (14365221025 : ℚ) / 330186251854371762

def SurrogateDiagonalTailChunk001Sub000Block181Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23971
    = surrogateDiagTailX0RatChunk001Sub000Block181Part019

theorem surrogateDiagonalTailChunk001Sub000Block181Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part019] using hcert

def TailChunk001Sub000Block181Part020SupportExplicit : Finset ℕ :=
  ([23973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part020 : ℚ :=
  (51066879881 : ℚ) / 493632786816000000

def SurrogateDiagonalTailChunk001Sub000Block181Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23973
    = surrogateDiagTailX0RatChunk001Sub000Block181Part020

theorem surrogateDiagonalTailChunk001Sub000Block181Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part020] using hcert

def TailChunk001Sub000Block181Part021SupportExplicit : Finset ℕ :=
  ([23974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part021 : ℚ :=
  (2245127640625 : ℚ) / 12902205682855550802

def SurrogateDiagonalTailChunk001Sub000Block181Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23974
    = surrogateDiagTailX0RatChunk001Sub000Block181Part021

theorem surrogateDiagonalTailChunk001Sub000Block181Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part021] using hcert

def TailChunk001Sub000Block181Part022SupportExplicit : Finset ℕ :=
  ([23977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part022 : ℚ :=
  (8982758265625 : ℚ) / 206573109691433513472

def SurrogateDiagonalTailChunk001Sub000Block181Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23977
    = surrogateDiagTailX0RatChunk001Sub000Block181Part022

theorem surrogateDiagonalTailChunk001Sub000Block181Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part022] using hcert

def TailChunk001Sub000Block181Part023SupportExplicit : Finset ℕ :=
  ([23978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part023 : ℚ :=
  (579718541 : ℚ) / 2917131517641600

def SurrogateDiagonalTailChunk001Sub000Block181Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23978
    = surrogateDiagTailX0RatChunk001Sub000Block181Part023

theorem surrogateDiagonalTailChunk001Sub000Block181Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part023] using hcert

def TailChunk001Sub000Block181Part024SupportExplicit : Finset ℕ :=
  ([23979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block181Part024 : ℚ :=
  (15968640200725 : ℚ) / 163218259509280800768

def SurrogateDiagonalTailChunk001Sub000Block181Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23979
    = surrogateDiagTailX0RatChunk001Sub000Block181Part024

theorem surrogateDiagonalTailChunk001Sub000Block181Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block181Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block181Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block181Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block181Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block181Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block181HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block181Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block181Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block181Part000
    + surrogateDiagTailX0RatChunk001Sub000Block181Part001
    + surrogateDiagTailX0RatChunk001Sub000Block181Part002
    + surrogateDiagTailX0RatChunk001Sub000Block181Part003
    + surrogateDiagTailX0RatChunk001Sub000Block181Part004
    + surrogateDiagTailX0RatChunk001Sub000Block181Part005
    + surrogateDiagTailX0RatChunk001Sub000Block181Part006
    + surrogateDiagTailX0RatChunk001Sub000Block181Part007
    + surrogateDiagTailX0RatChunk001Sub000Block181Part008
    + surrogateDiagTailX0RatChunk001Sub000Block181Part009

def surrogateDiagonalTailChunk001Sub000Block181MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block181Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block181Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block181Part010
    + surrogateDiagTailX0RatChunk001Sub000Block181Part011
    + surrogateDiagTailX0RatChunk001Sub000Block181Part012
    + surrogateDiagTailX0RatChunk001Sub000Block181Part013
    + surrogateDiagTailX0RatChunk001Sub000Block181Part014
    + surrogateDiagTailX0RatChunk001Sub000Block181Part015
    + surrogateDiagTailX0RatChunk001Sub000Block181Part016
    + surrogateDiagTailX0RatChunk001Sub000Block181Part017
    + surrogateDiagTailX0RatChunk001Sub000Block181Part018
    + surrogateDiagTailX0RatChunk001Sub000Block181Part019

def surrogateDiagonalTailChunk001Sub000Block181TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block181Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block181Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block181Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block181Part020
    + surrogateDiagTailX0RatChunk001Sub000Block181Part021
    + surrogateDiagTailX0RatChunk001Sub000Block181Part022
    + surrogateDiagTailX0RatChunk001Sub000Block181Part023
    + surrogateDiagTailX0RatChunk001Sub000Block181Part024

def surrogateDiagonalTailChunk001Sub000Block181Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block181HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block181MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block181TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block181 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block181Part000
    + surrogateDiagTailX0RatChunk001Sub000Block181Part001
    + surrogateDiagTailX0RatChunk001Sub000Block181Part002
    + surrogateDiagTailX0RatChunk001Sub000Block181Part003
    + surrogateDiagTailX0RatChunk001Sub000Block181Part004
    + surrogateDiagTailX0RatChunk001Sub000Block181Part005
    + surrogateDiagTailX0RatChunk001Sub000Block181Part006
    + surrogateDiagTailX0RatChunk001Sub000Block181Part007
    + surrogateDiagTailX0RatChunk001Sub000Block181Part008
    + surrogateDiagTailX0RatChunk001Sub000Block181Part009
    + surrogateDiagTailX0RatChunk001Sub000Block181Part010
    + surrogateDiagTailX0RatChunk001Sub000Block181Part011
    + surrogateDiagTailX0RatChunk001Sub000Block181Part012
    + surrogateDiagTailX0RatChunk001Sub000Block181Part013
    + surrogateDiagTailX0RatChunk001Sub000Block181Part014
    + surrogateDiagTailX0RatChunk001Sub000Block181Part015
    + surrogateDiagTailX0RatChunk001Sub000Block181Part016
    + surrogateDiagTailX0RatChunk001Sub000Block181Part017
    + surrogateDiagTailX0RatChunk001Sub000Block181Part018
    + surrogateDiagTailX0RatChunk001Sub000Block181Part019
    + surrogateDiagTailX0RatChunk001Sub000Block181Part020
    + surrogateDiagTailX0RatChunk001Sub000Block181Part021
    + surrogateDiagTailX0RatChunk001Sub000Block181Part022
    + surrogateDiagTailX0RatChunk001Sub000Block181Part023
    + surrogateDiagTailX0RatChunk001Sub000Block181Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block181_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block181Head + surrogateDiagTailX0RatChunk001Sub000Block181Mid + surrogateDiagTailX0RatChunk001Sub000Block181Tail =
      surrogateDiagTailX0RatChunk001Sub000Block181 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block181Head surrogateDiagTailX0RatChunk001Sub000Block181Mid surrogateDiagTailX0RatChunk001Sub000Block181Tail surrogateDiagTailX0RatChunk001Sub000Block181
  ring

def SurrogateDiagonalTailChunk001Sub000Block181HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block181HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block181Head

def SurrogateDiagonalTailChunk001Sub000Block181MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block181MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block181Mid

def SurrogateDiagonalTailChunk001Sub000Block181TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block181TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block181Tail

theorem surrogateDiagonalTailChunk001Sub000Block181_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block181HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block181MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block181TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block181Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block181 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block181HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block181MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block181TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block181Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block181_eq_head_add_mid_add_tail

/-- Block 182 covers tail-support indices [14550,14575) and q from 23981 to 24022. -/

def TailChunk001Sub000Block182Part000SupportExplicit : Finset ℕ :=
  ([23981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part000 : ℚ :=
  (14377209025 : ℚ) / 330737595924486432

def SurrogateDiagonalTailChunk001Sub000Block182Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23981
    = surrogateDiagTailX0RatChunk001Sub000Block182Part000

theorem surrogateDiagonalTailChunk001Sub000Block182Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part000] using hcert

def TailChunk001Sub000Block182Part001SupportExplicit : Finset ℕ :=
  ([23982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part001 : ℚ :=
  (64239402497 : ℚ) / 109466507291673600

def SurrogateDiagonalTailChunk001Sub000Block182Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23982
    = surrogateDiagTailX0RatChunk001Sub000Block182Part001

theorem surrogateDiagonalTailChunk001Sub000Block182Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part001] using hcert

def TailChunk001Sub000Block182Part002SupportExplicit : Finset ℕ :=
  ([23983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part002 : ℚ :=
  (8413904442175 : ℚ) / 178862452851514962432

def SurrogateDiagonalTailChunk001Sub000Block182Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23983
    = surrogateDiagTailX0RatChunk001Sub000Block182Part002

theorem surrogateDiagonalTailChunk001Sub000Block182Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part002] using hcert

def TailChunk001Sub000Block182Part003SupportExplicit : Finset ℕ :=
  ([23986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part003 : ℚ :=
  (87889125425 : ℚ) / 481113358591992192

def SurrogateDiagonalTailChunk001Sub000Block182Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23986
    = surrogateDiagTailX0RatChunk001Sub000Block182Part003

theorem surrogateDiagonalTailChunk001Sub000Block182Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part003] using hcert

def TailChunk001Sub000Block182Part004SupportExplicit : Finset ℕ :=
  ([23989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part004 : ℚ :=
  (86086533325 : ℚ) / 1264669245814588416

def SurrogateDiagonalTailChunk001Sub000Block182Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23989
    = surrogateDiagTailX0RatChunk001Sub000Block182Part004

theorem surrogateDiagonalTailChunk001Sub000Block182Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part004] using hcert

def TailChunk001Sub000Block182Part005SupportExplicit : Finset ℕ :=
  ([23990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part005 : ℚ :=
  (6111629657725 : ℚ) / 21167206139167131648

def SurrogateDiagonalTailChunk001Sub000Block182Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23990
    = surrogateDiagTailX0RatChunk001Sub000Block182Part005

theorem surrogateDiagonalTailChunk001Sub000Block182Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part005] using hcert

def TailChunk001Sub000Block182Part006SupportExplicit : Finset ℕ :=
  ([23991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part006 : ℚ :=
  (179717629961 : ℚ) / 1481944915189094400

def SurrogateDiagonalTailChunk001Sub000Block182Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23991
    = surrogateDiagTailX0RatChunk001Sub000Block182Part006

theorem surrogateDiagonalTailChunk001Sub000Block182Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part006] using hcert

def TailChunk001Sub000Block182Part007SupportExplicit : Finset ℕ :=
  ([23993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part007 : ℚ :=
  (8994750765625 : ℚ) / 207125074940924416512

def SurrogateDiagonalTailChunk001Sub000Block182Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23993
    = surrogateDiagTailX0RatChunk001Sub000Block182Part007

theorem surrogateDiagonalTailChunk001Sub000Block182Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part007] using hcert

def TailChunk001Sub000Block182Part008SupportExplicit : Finset ℕ :=
  ([23995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part008 : ℚ :=
  (1438878390625 : ℚ) / 21202536331591091328

def SurrogateDiagonalTailChunk001Sub000Block182Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23995
    = surrogateDiagTailX0RatChunk001Sub000Block182Part008

theorem surrogateDiagonalTailChunk001Sub000Block182Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part008] using hcert

def TailChunk001Sub000Block182Part009SupportExplicit : Finset ℕ :=
  ([23997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part009 : ℚ :=
  (580791763933 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub000Block182Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23997
    = surrogateDiagTailX0RatChunk001Sub000Block182Part009

theorem surrogateDiagonalTailChunk001Sub000Block182Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part009] using hcert

def TailChunk001Sub000Block182Part010SupportExplicit : Finset ℕ :=
  ([23999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part010 : ℚ :=
  (114716048375 : ℚ) / 2562465689255559168

def SurrogateDiagonalTailChunk001Sub000Block182Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23999
    = surrogateDiagTailX0RatChunk001Sub000Block182Part010

theorem surrogateDiagonalTailChunk001Sub000Block182Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part010] using hcert

def TailChunk001Sub000Block182Part011SupportExplicit : Finset ℕ :=
  ([24001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part011 : ℚ :=
  (576048001 : ℚ) / 13273694208000000

def SurrogateDiagonalTailChunk001Sub000Block182Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24001
    = surrogateDiagTailX0RatChunk001Sub000Block182Part011

theorem surrogateDiagonalTailChunk001Sub000Block182Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part011] using hcert

def TailChunk001Sub000Block182Part012SupportExplicit : Finset ℕ :=
  ([24002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part012 : ℚ :=
  (306092688277 : ℚ) / 1411863926322000000

def SurrogateDiagonalTailChunk001Sub000Block182Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24002
    = surrogateDiagTailX0RatChunk001Sub000Block182Part012

theorem surrogateDiagonalTailChunk001Sub000Block182Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part012] using hcert

def TailChunk001Sub000Block182Part013SupportExplicit : Finset ℕ :=
  ([24005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part013 : ℚ :=
  (30721667 : ℚ) / 453075428966400

def SurrogateDiagonalTailChunk001Sub000Block182Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24005
    = surrogateDiagTailX0RatChunk001Sub000Block182Part013

theorem surrogateDiagonalTailChunk001Sub000Block182Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part013] using hcert

def TailChunk001Sub000Block182Part014SupportExplicit : Finset ℕ :=
  ([24006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part014 : ℚ :=
  (100028496749 : ℚ) / 204840960000000000

def SurrogateDiagonalTailChunk001Sub000Block182Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24006
    = surrogateDiagTailX0RatChunk001Sub000Block182Part014

theorem surrogateDiagonalTailChunk001Sub000Block182Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part014] using hcert

def TailChunk001Sub000Block182Part015SupportExplicit : Finset ℕ :=
  ([24007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part015 : ℚ :=
  (9005250765625 : ℚ) / 207608951260515402162

def SurrogateDiagonalTailChunk001Sub000Block182Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24007
    = surrogateDiagTailX0RatChunk001Sub000Block182Part015

theorem surrogateDiagonalTailChunk001Sub000Block182Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part015] using hcert

def TailChunk001Sub000Block182Part016SupportExplicit : Finset ℕ :=
  ([24009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part016 : ℚ :=
  (306585689297 : ℚ) / 2961796720896000000

def SurrogateDiagonalTailChunk001Sub000Block182Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24009
    = surrogateDiagTailX0RatChunk001Sub000Block182Part016

theorem surrogateDiagonalTailChunk001Sub000Block182Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part016] using hcert

def TailChunk001Sub000Block182Part017SupportExplicit : Finset ℕ :=
  ([24011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part017 : ℚ :=
  (31101110291125 : ℚ) / 602113867666041489408

def SurrogateDiagonalTailChunk001Sub000Block182Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24011
    = surrogateDiagTailX0RatChunk001Sub000Block182Part017

theorem surrogateDiagonalTailChunk001Sub000Block182Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part017] using hcert

def TailChunk001Sub000Block182Part018SupportExplicit : Finset ℕ :=
  ([24013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part018 : ℚ :=
  (1111471169521 : ℚ) / 19011169219085107200

def SurrogateDiagonalTailChunk001Sub000Block182Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24013
    = surrogateDiagTailX0RatChunk001Sub000Block182Part018

theorem surrogateDiagonalTailChunk001Sub000Block182Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part018] using hcert

def TailChunk001Sub000Block182Part019SupportExplicit : Finset ℕ :=
  ([24014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part019 : ℚ :=
  (2252625765625 : ℚ) / 12988536634370106162

def SurrogateDiagonalTailChunk001Sub000Block182Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24014
    = surrogateDiagTailX0RatChunk001Sub000Block182Part019

theorem surrogateDiagonalTailChunk001Sub000Block182Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part019] using hcert

def TailChunk001Sub000Block182Part020SupportExplicit : Finset ℕ :=
  ([24015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part020 : ℚ :=
  (17602334157 : ℚ) / 111870476288000000

def SurrogateDiagonalTailChunk001Sub000Block182Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24015
    = surrogateDiagTailX0RatChunk001Sub000Block182Part020

theorem surrogateDiagonalTailChunk001Sub000Block182Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part020] using hcert

def TailChunk001Sub000Block182Part021SupportExplicit : Finset ℕ :=
  ([24017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part021 : ℚ :=
  (25571898711325 : ℚ) / 389935856817736777728

def SurrogateDiagonalTailChunk001Sub000Block182Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24017
    = surrogateDiagTailX0RatChunk001Sub000Block182Part021

theorem surrogateDiagonalTailChunk001Sub000Block182Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part021] using hcert

def TailChunk001Sub000Block182Part022SupportExplicit : Finset ℕ :=
  ([24018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part022 : ℚ :=
  (312901680475 : ℚ) / 641409216512104008

def SurrogateDiagonalTailChunk001Sub000Block182Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24018
    = surrogateDiagTailX0RatChunk001Sub000Block182Part022

theorem surrogateDiagonalTailChunk001Sub000Block182Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part022] using hcert

def TailChunk001Sub000Block182Part023SupportExplicit : Finset ℕ :=
  ([24019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part023 : ℚ :=
  (9014255640625 : ℚ) / 208024376746023607122

def SurrogateDiagonalTailChunk001Sub000Block182Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24019
    = surrogateDiagTailX0RatChunk001Sub000Block182Part023

theorem surrogateDiagonalTailChunk001Sub000Block182Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part023] using hcert

def TailChunk001Sub000Block182Part024SupportExplicit : Finset ℕ :=
  ([24022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block182Part024 : ℚ :=
  (3606603025 : ℚ) / 20809367489299602

def SurrogateDiagonalTailChunk001Sub000Block182Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24022
    = surrogateDiagTailX0RatChunk001Sub000Block182Part024

theorem surrogateDiagonalTailChunk001Sub000Block182Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block182Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block182Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block182Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block182Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block182Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block182HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block182Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block182Part000
    + surrogateDiagTailX0RatChunk001Sub000Block182Part001
    + surrogateDiagTailX0RatChunk001Sub000Block182Part002
    + surrogateDiagTailX0RatChunk001Sub000Block182Part003
    + surrogateDiagTailX0RatChunk001Sub000Block182Part004
    + surrogateDiagTailX0RatChunk001Sub000Block182Part005
    + surrogateDiagTailX0RatChunk001Sub000Block182Part006
    + surrogateDiagTailX0RatChunk001Sub000Block182Part007
    + surrogateDiagTailX0RatChunk001Sub000Block182Part008
    + surrogateDiagTailX0RatChunk001Sub000Block182Part009

def surrogateDiagonalTailChunk001Sub000Block182MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block182Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block182Part010
    + surrogateDiagTailX0RatChunk001Sub000Block182Part011
    + surrogateDiagTailX0RatChunk001Sub000Block182Part012
    + surrogateDiagTailX0RatChunk001Sub000Block182Part013
    + surrogateDiagTailX0RatChunk001Sub000Block182Part014
    + surrogateDiagTailX0RatChunk001Sub000Block182Part015
    + surrogateDiagTailX0RatChunk001Sub000Block182Part016
    + surrogateDiagTailX0RatChunk001Sub000Block182Part017
    + surrogateDiagTailX0RatChunk001Sub000Block182Part018
    + surrogateDiagTailX0RatChunk001Sub000Block182Part019

def surrogateDiagonalTailChunk001Sub000Block182TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block182Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block182Part020
    + surrogateDiagTailX0RatChunk001Sub000Block182Part021
    + surrogateDiagTailX0RatChunk001Sub000Block182Part022
    + surrogateDiagTailX0RatChunk001Sub000Block182Part023
    + surrogateDiagTailX0RatChunk001Sub000Block182Part024

def surrogateDiagonalTailChunk001Sub000Block182Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block182HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block182MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block182TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block182 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block182Part000
    + surrogateDiagTailX0RatChunk001Sub000Block182Part001
    + surrogateDiagTailX0RatChunk001Sub000Block182Part002
    + surrogateDiagTailX0RatChunk001Sub000Block182Part003
    + surrogateDiagTailX0RatChunk001Sub000Block182Part004
    + surrogateDiagTailX0RatChunk001Sub000Block182Part005
    + surrogateDiagTailX0RatChunk001Sub000Block182Part006
    + surrogateDiagTailX0RatChunk001Sub000Block182Part007
    + surrogateDiagTailX0RatChunk001Sub000Block182Part008
    + surrogateDiagTailX0RatChunk001Sub000Block182Part009
    + surrogateDiagTailX0RatChunk001Sub000Block182Part010
    + surrogateDiagTailX0RatChunk001Sub000Block182Part011
    + surrogateDiagTailX0RatChunk001Sub000Block182Part012
    + surrogateDiagTailX0RatChunk001Sub000Block182Part013
    + surrogateDiagTailX0RatChunk001Sub000Block182Part014
    + surrogateDiagTailX0RatChunk001Sub000Block182Part015
    + surrogateDiagTailX0RatChunk001Sub000Block182Part016
    + surrogateDiagTailX0RatChunk001Sub000Block182Part017
    + surrogateDiagTailX0RatChunk001Sub000Block182Part018
    + surrogateDiagTailX0RatChunk001Sub000Block182Part019
    + surrogateDiagTailX0RatChunk001Sub000Block182Part020
    + surrogateDiagTailX0RatChunk001Sub000Block182Part021
    + surrogateDiagTailX0RatChunk001Sub000Block182Part022
    + surrogateDiagTailX0RatChunk001Sub000Block182Part023
    + surrogateDiagTailX0RatChunk001Sub000Block182Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block182_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block182Head + surrogateDiagTailX0RatChunk001Sub000Block182Mid + surrogateDiagTailX0RatChunk001Sub000Block182Tail =
      surrogateDiagTailX0RatChunk001Sub000Block182 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block182Head surrogateDiagTailX0RatChunk001Sub000Block182Mid surrogateDiagTailX0RatChunk001Sub000Block182Tail surrogateDiagTailX0RatChunk001Sub000Block182
  ring

def SurrogateDiagonalTailChunk001Sub000Block182HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block182HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block182Head

def SurrogateDiagonalTailChunk001Sub000Block182MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block182MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block182Mid

def SurrogateDiagonalTailChunk001Sub000Block182TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block182TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block182Tail

theorem surrogateDiagonalTailChunk001Sub000Block182_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block182HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block182MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block182TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block182Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block182 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block182HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block182MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block182TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block182Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block182_eq_head_add_mid_add_tail

/-- Block 183 covers tail-support indices [14575,14600) and q from 24023 to 24065. -/

def TailChunk001Sub000Block183Part000SupportExplicit : Finset ℕ :=
  ([24023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part000 : ℚ :=
  (9017258265625 : ℚ) / 208162990352242215282

def SurrogateDiagonalTailChunk001Sub000Block183Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24023
    = surrogateDiagTailX0RatChunk001Sub000Block183Part000

theorem surrogateDiagonalTailChunk001Sub000Block183Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part000] using hcert

def TailChunk001Sub000Block183Part001SupportExplicit : Finset ℕ :=
  ([24026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part001 : ℚ :=
  (345006992563 : ℚ) / 1861479343600435200

def SurrogateDiagonalTailChunk001Sub000Block183Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24026
    = surrogateDiagTailX0RatChunk001Sub000Block183Part001

theorem surrogateDiagonalTailChunk001Sub000Block183Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part001] using hcert

def TailChunk001Sub000Block183Part002SupportExplicit : Finset ℕ :=
  ([24027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part002 : ℚ :=
  (1457512745375 : ℚ) / 14957203905842085888

def SurrogateDiagonalTailChunk001Sub000Block183Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24027
    = surrogateDiagTailX0RatChunk001Sub000Block183Part002

theorem surrogateDiagonalTailChunk001Sub000Block183Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part002] using hcert

def TailChunk001Sub000Block183Part003SupportExplicit : Finset ℕ :=
  ([24029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part003 : ℚ :=
  (9021763140625 : ℚ) / 208371040632455660832

def SurrogateDiagonalTailChunk001Sub000Block183Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24029
    = surrogateDiagTailX0RatChunk001Sub000Block183Part003

theorem surrogateDiagonalTailChunk001Sub000Block183Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part003] using hcert

def TailChunk001Sub000Block183Part004SupportExplicit : Finset ℕ :=
  ([24031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part004 : ℚ :=
  (27241703860225 : ℚ) / 449594486917338267648

def SurrogateDiagonalTailChunk001Sub000Block183Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24031
    = surrogateDiagTailX0RatChunk001Sub000Block183Part004

theorem surrogateDiagonalTailChunk001Sub000Block183Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part004] using hcert

def TailChunk001Sub000Block183Part005SupportExplicit : Finset ℕ :=
  ([24033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part005 : ℚ :=
  (641625967957 : ℚ) / 6587746777114243200

def SurrogateDiagonalTailChunk001Sub000Block183Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24033
    = surrogateDiagTailX0RatChunk001Sub000Block183Part005

theorem surrogateDiagonalTailChunk001Sub000Block183Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part005] using hcert

def TailChunk001Sub000Block183Part006SupportExplicit : Finset ℕ :=
  ([24034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part006 : ℚ :=
  (348834814399 : ℚ) / 1913005141099315200

def SurrogateDiagonalTailChunk001Sub000Block183Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24034
    = surrogateDiagTailX0RatChunk001Sub000Block183Part006

theorem surrogateDiagonalTailChunk001Sub000Block183Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part006] using hcert

def TailChunk001Sub000Block183Part007SupportExplicit : Finset ℕ :=
  ([24035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part007 : ℚ :=
  (659498918839 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk001Sub000Block183Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24035
    = surrogateDiagTailX0RatChunk001Sub000Block183Part007

theorem surrogateDiagonalTailChunk001Sub000Block183Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part007] using hcert

def TailChunk001Sub000Block183Part008SupportExplicit : Finset ℕ :=
  ([24038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part008 : ℚ :=
  (5573899163 : ℚ) / 18878142873600000

def SurrogateDiagonalTailChunk001Sub000Block183Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24038
    = surrogateDiagTailX0RatChunk001Sub000Block183Part008

theorem surrogateDiagonalTailChunk001Sub000Block183Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part008] using hcert

def TailChunk001Sub000Block183Part009SupportExplicit : Finset ℕ :=
  ([24041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part009 : ℚ :=
  (34792957025 : ℚ) / 743214315827257344

def SurrogateDiagonalTailChunk001Sub000Block183Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24041
    = surrogateDiagTailX0RatChunk001Sub000Block183Part009

theorem surrogateDiagonalTailChunk001Sub000Block183Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part009] using hcert

def TailChunk001Sub000Block183Part010SupportExplicit : Finset ℕ :=
  ([24042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part010 : ℚ :=
  (1254109622275 : ℚ) / 2575909673491874592

def SurrogateDiagonalTailChunk001Sub000Block183Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24042
    = surrogateDiagTailX0RatChunk001Sub000Block183Part010

theorem surrogateDiagonalTailChunk001Sub000Block183Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part010] using hcert

def TailChunk001Sub000Block183Part011SupportExplicit : Finset ℕ :=
  ([24043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part011 : ℚ :=
  (9032278890625 : ℚ) / 208857097754162254962

def SurrogateDiagonalTailChunk001Sub000Block183Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24043
    = surrogateDiagTailX0RatChunk001Sub000Block183Part011

theorem surrogateDiagonalTailChunk001Sub000Block183Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part011] using hcert

def TailChunk001Sub000Block183Part012SupportExplicit : Finset ℕ :=
  ([24045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part012 : ℚ :=
  (4330184068475 : ℚ) / 17934992554667802624

def SurrogateDiagonalTailChunk001Sub000Block183Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24045
    = surrogateDiagTailX0RatChunk001Sub000Block183Part012

theorem surrogateDiagonalTailChunk001Sub000Block183Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part012] using hcert

def TailChunk001Sub000Block183Part013SupportExplicit : Finset ℕ :=
  ([24046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part013 : ℚ :=
  (310206050641 : ℚ) / 1422254785374259200

def SurrogateDiagonalTailChunk001Sub000Block183Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24046
    = surrogateDiagTailX0RatChunk001Sub000Block183Part013

theorem surrogateDiagonalTailChunk001Sub000Block183Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part013] using hcert

def TailChunk001Sub000Block183Part014SupportExplicit : Finset ℕ :=
  ([24047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part014 : ℚ :=
  (767578939075 : ℚ) / 17254372133200002048

def SurrogateDiagonalTailChunk001Sub000Block183Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24047
    = surrogateDiagTailX0RatChunk001Sub000Block183Part014

theorem surrogateDiagonalTailChunk001Sub000Block183Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part014] using hcert

def TailChunk001Sub000Block183Part015SupportExplicit : Finset ℕ :=
  ([24049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block183Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24049
    = surrogateDiagTailX0RatChunk001Sub000Block183Part015

theorem surrogateDiagonalTailChunk001Sub000Block183Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part015] using hcert

def TailChunk001Sub000Block183Part016SupportExplicit : Finset ℕ :=
  ([24051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part016 : ℚ :=
  (41675 : ℚ) / 11010310493700096

def SurrogateDiagonalTailChunk001Sub000Block183Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24051
    = surrogateDiagTailX0RatChunk001Sub000Block183Part016

theorem surrogateDiagonalTailChunk001Sub000Block183Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part016] using hcert

def TailChunk001Sub000Block183Part017SupportExplicit : Finset ℕ :=
  ([24053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part017 : ℚ :=
  (16572130325 : ℚ) / 97419236290243875216

def SurrogateDiagonalTailChunk001Sub000Block183Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24053
    = surrogateDiagTailX0RatChunk001Sub000Block183Part017

theorem surrogateDiagonalTailChunk001Sub000Block183Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part017] using hcert

def TailChunk001Sub000Block183Part018SupportExplicit : Finset ℕ :=
  ([24054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part018 : ℚ :=
  (10338134521 : ℚ) / 81679682493964800

def SurrogateDiagonalTailChunk001Sub000Block183Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24054
    = surrogateDiagTailX0RatChunk001Sub000Block183Part018

theorem surrogateDiagonalTailChunk001Sub000Block183Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part018] using hcert

def TailChunk001Sub000Block183Part019SupportExplicit : Finset ℕ :=
  ([24055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part019 : ℚ :=
  (59284575625 : ℚ) / 9826060276863074304

def SurrogateDiagonalTailChunk001Sub000Block183Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24055
    = surrogateDiagTailX0RatChunk001Sub000Block183Part019

theorem surrogateDiagonalTailChunk001Sub000Block183Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part019] using hcert

def TailChunk001Sub000Block183Part020SupportExplicit : Finset ℕ :=
  ([24058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part020 : ℚ :=
  (5513489375 : ℚ) / 1499690347718884992

def SurrogateDiagonalTailChunk001Sub000Block183Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24058
    = surrogateDiagTailX0RatChunk001Sub000Block183Part020

theorem surrogateDiagonalTailChunk001Sub000Block183Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part020] using hcert

def TailChunk001Sub000Block183Part021SupportExplicit : Finset ℕ :=
  ([24061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block183Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24061
    = surrogateDiagTailX0RatChunk001Sub000Block183Part021

theorem surrogateDiagonalTailChunk001Sub000Block183Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part021] using hcert

def TailChunk001Sub000Block183Part022SupportExplicit : Finset ℕ :=
  ([24062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part022 : ℚ :=
  (14381843025 : ℚ) / 7949187475893767168

def SurrogateDiagonalTailChunk001Sub000Block183Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24062
    = surrogateDiagTailX0RatChunk001Sub000Block183Part022

theorem surrogateDiagonalTailChunk001Sub000Block183Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part022] using hcert

def TailChunk001Sub000Block183Part023SupportExplicit : Finset ℕ :=
  ([24063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part023 : ℚ :=
  (339569654125 : ℚ) / 119452343479113351168

def SurrogateDiagonalTailChunk001Sub000Block183Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24063
    = surrogateDiagTailX0RatChunk001Sub000Block183Part023

theorem surrogateDiagonalTailChunk001Sub000Block183Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part023] using hcert

def TailChunk001Sub000Block183Part024SupportExplicit : Finset ℕ :=
  ([24065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block183Part024 : ℚ :=
  (1448459585875 : ℚ) / 343217401439672107008

def SurrogateDiagonalTailChunk001Sub000Block183Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24065
    = surrogateDiagTailX0RatChunk001Sub000Block183Part024

theorem surrogateDiagonalTailChunk001Sub000Block183Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block183Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block183Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block183Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block183Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block183Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block183HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block183Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block183Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block183Part000
    + surrogateDiagTailX0RatChunk001Sub000Block183Part001
    + surrogateDiagTailX0RatChunk001Sub000Block183Part002
    + surrogateDiagTailX0RatChunk001Sub000Block183Part003
    + surrogateDiagTailX0RatChunk001Sub000Block183Part004
    + surrogateDiagTailX0RatChunk001Sub000Block183Part005
    + surrogateDiagTailX0RatChunk001Sub000Block183Part006
    + surrogateDiagTailX0RatChunk001Sub000Block183Part007
    + surrogateDiagTailX0RatChunk001Sub000Block183Part008
    + surrogateDiagTailX0RatChunk001Sub000Block183Part009

def surrogateDiagonalTailChunk001Sub000Block183MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block183Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block183Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block183Part010
    + surrogateDiagTailX0RatChunk001Sub000Block183Part011
    + surrogateDiagTailX0RatChunk001Sub000Block183Part012
    + surrogateDiagTailX0RatChunk001Sub000Block183Part013
    + surrogateDiagTailX0RatChunk001Sub000Block183Part014
    + surrogateDiagTailX0RatChunk001Sub000Block183Part015
    + surrogateDiagTailX0RatChunk001Sub000Block183Part016
    + surrogateDiagTailX0RatChunk001Sub000Block183Part017
    + surrogateDiagTailX0RatChunk001Sub000Block183Part018
    + surrogateDiagTailX0RatChunk001Sub000Block183Part019

def surrogateDiagonalTailChunk001Sub000Block183TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block183Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block183Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block183Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block183Part020
    + surrogateDiagTailX0RatChunk001Sub000Block183Part021
    + surrogateDiagTailX0RatChunk001Sub000Block183Part022
    + surrogateDiagTailX0RatChunk001Sub000Block183Part023
    + surrogateDiagTailX0RatChunk001Sub000Block183Part024

def surrogateDiagonalTailChunk001Sub000Block183Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block183HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block183MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block183TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block183 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block183Part000
    + surrogateDiagTailX0RatChunk001Sub000Block183Part001
    + surrogateDiagTailX0RatChunk001Sub000Block183Part002
    + surrogateDiagTailX0RatChunk001Sub000Block183Part003
    + surrogateDiagTailX0RatChunk001Sub000Block183Part004
    + surrogateDiagTailX0RatChunk001Sub000Block183Part005
    + surrogateDiagTailX0RatChunk001Sub000Block183Part006
    + surrogateDiagTailX0RatChunk001Sub000Block183Part007
    + surrogateDiagTailX0RatChunk001Sub000Block183Part008
    + surrogateDiagTailX0RatChunk001Sub000Block183Part009
    + surrogateDiagTailX0RatChunk001Sub000Block183Part010
    + surrogateDiagTailX0RatChunk001Sub000Block183Part011
    + surrogateDiagTailX0RatChunk001Sub000Block183Part012
    + surrogateDiagTailX0RatChunk001Sub000Block183Part013
    + surrogateDiagTailX0RatChunk001Sub000Block183Part014
    + surrogateDiagTailX0RatChunk001Sub000Block183Part015
    + surrogateDiagTailX0RatChunk001Sub000Block183Part016
    + surrogateDiagTailX0RatChunk001Sub000Block183Part017
    + surrogateDiagTailX0RatChunk001Sub000Block183Part018
    + surrogateDiagTailX0RatChunk001Sub000Block183Part019
    + surrogateDiagTailX0RatChunk001Sub000Block183Part020
    + surrogateDiagTailX0RatChunk001Sub000Block183Part021
    + surrogateDiagTailX0RatChunk001Sub000Block183Part022
    + surrogateDiagTailX0RatChunk001Sub000Block183Part023
    + surrogateDiagTailX0RatChunk001Sub000Block183Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block183_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block183Head + surrogateDiagTailX0RatChunk001Sub000Block183Mid + surrogateDiagTailX0RatChunk001Sub000Block183Tail =
      surrogateDiagTailX0RatChunk001Sub000Block183 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block183Head surrogateDiagTailX0RatChunk001Sub000Block183Mid surrogateDiagTailX0RatChunk001Sub000Block183Tail surrogateDiagTailX0RatChunk001Sub000Block183
  ring

def SurrogateDiagonalTailChunk001Sub000Block183HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block183HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block183Head

def SurrogateDiagonalTailChunk001Sub000Block183MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block183MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block183Mid

def SurrogateDiagonalTailChunk001Sub000Block183TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block183TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block183Tail

theorem surrogateDiagonalTailChunk001Sub000Block183_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block183HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block183MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block183TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block183Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block183 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block183HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block183MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block183TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block183Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block183_eq_head_add_mid_add_tail

/-- Block 184 covers tail-support indices [14600,14625) and q from 24067 to 24105. -/

def TailChunk001Sub000Block184Part000SupportExplicit : Finset ℕ :=
  ([24067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part000 : ℚ :=
  (8214269989 : ℚ) / 30193765626512179200

def SurrogateDiagonalTailChunk001Sub000Block184Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24067
    = surrogateDiagTailX0RatChunk001Sub000Block184Part000

theorem surrogateDiagonalTailChunk001Sub000Block184Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part000] using hcert

def TailChunk001Sub000Block184Part001SupportExplicit : Finset ℕ :=
  ([24069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part001 : ℚ :=
  (568811237 : ℚ) / 755755117471334400

def SurrogateDiagonalTailChunk001Sub000Block184Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24069
    = surrogateDiagTailX0RatChunk001Sub000Block184Part001

theorem surrogateDiagonalTailChunk001Sub000Block184Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part001] using hcert

def TailChunk001Sub000Block184Part002SupportExplicit : Finset ℕ :=
  ([24070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part002 : ℚ :=
  (33056726175 : ℚ) / 741213153026834432

def SurrogateDiagonalTailChunk001Sub000Block184Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24070
    = surrogateDiagTailX0RatChunk001Sub000Block184Part002

theorem surrogateDiagonalTailChunk001Sub000Block184Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part002] using hcert

def TailChunk001Sub000Block184Part003SupportExplicit : Finset ℕ :=
  ([24071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24071
    = surrogateDiagTailX0RatChunk001Sub000Block184Part003

theorem surrogateDiagonalTailChunk001Sub000Block184Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part003] using hcert

def TailChunk001Sub000Block184Part004SupportExplicit : Finset ℕ :=
  ([24073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part004 : ℚ :=
  (4567265621 : ℚ) / 1587191697808588800

def SurrogateDiagonalTailChunk001Sub000Block184Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24073
    = surrogateDiagTailX0RatChunk001Sub000Block184Part004

theorem surrogateDiagonalTailChunk001Sub000Block184Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part004] using hcert

def TailChunk001Sub000Block184Part005SupportExplicit : Finset ℕ :=
  ([24074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24074
    = surrogateDiagTailX0RatChunk001Sub000Block184Part005

theorem surrogateDiagonalTailChunk001Sub000Block184Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part005] using hcert

def TailChunk001Sub000Block184Part006SupportExplicit : Finset ℕ :=
  ([24077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24077
    = surrogateDiagTailX0RatChunk001Sub000Block184Part006

theorem surrogateDiagonalTailChunk001Sub000Block184Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part006] using hcert

def TailChunk001Sub000Block184Part007SupportExplicit : Finset ℕ :=
  ([24078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part007 : ℚ :=
  (31457315225 : ℚ) / 323922086048837184

def SurrogateDiagonalTailChunk001Sub000Block184Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24078
    = surrogateDiagTailX0RatChunk001Sub000Block184Part007

theorem surrogateDiagonalTailChunk001Sub000Block184Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part007] using hcert

def TailChunk001Sub000Block184Part008SupportExplicit : Finset ℕ :=
  ([24081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part008 : ℚ :=
  (116620405325 : ℚ) / 68726550255956803584

def SurrogateDiagonalTailChunk001Sub000Block184Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24081
    = surrogateDiagTailX0RatChunk001Sub000Block184Part008

theorem surrogateDiagonalTailChunk001Sub000Block184Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part008] using hcert

def TailChunk001Sub000Block184Part009SupportExplicit : Finset ℕ :=
  ([24082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24082
    = surrogateDiagTailX0RatChunk001Sub000Block184Part009

theorem surrogateDiagonalTailChunk001Sub000Block184Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part009] using hcert

def TailChunk001Sub000Block184Part010SupportExplicit : Finset ℕ :=
  ([24083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24083
    = surrogateDiagTailX0RatChunk001Sub000Block184Part010

theorem surrogateDiagonalTailChunk001Sub000Block184Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part010] using hcert

def TailChunk001Sub000Block184Part011SupportExplicit : Finset ℕ :=
  ([24085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part011 : ℚ :=
  (483622195125 : ℚ) / 114786676723192692736

def SurrogateDiagonalTailChunk001Sub000Block184Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24085
    = surrogateDiagTailX0RatChunk001Sub000Block184Part011

theorem surrogateDiagonalTailChunk001Sub000Block184Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part011] using hcert

def TailChunk001Sub000Block184Part012SupportExplicit : Finset ℕ :=
  ([24086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24086
    = surrogateDiagTailX0RatChunk001Sub000Block184Part012

theorem surrogateDiagonalTailChunk001Sub000Block184Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part012] using hcert

def TailChunk001Sub000Block184Part013SupportExplicit : Finset ℕ :=
  ([24087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part013 : ℚ :=
  (80715601 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk001Sub000Block184Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24087
    = surrogateDiagTailX0RatChunk001Sub000Block184Part013

theorem surrogateDiagonalTailChunk001Sub000Block184Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part013] using hcert

def TailChunk001Sub000Block184Part014SupportExplicit : Finset ℕ :=
  ([24089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part014 : ℚ :=
  (356232246725 : ℚ) / 154101029789012852736

def SurrogateDiagonalTailChunk001Sub000Block184Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24089
    = surrogateDiagTailX0RatChunk001Sub000Block184Part014

theorem surrogateDiagonalTailChunk001Sub000Block184Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part014] using hcert

def TailChunk001Sub000Block184Part015SupportExplicit : Finset ℕ :=
  ([24090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part015 : ℚ :=
  (14334755227 : ℚ) / 36699109746278400

def SurrogateDiagonalTailChunk001Sub000Block184Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24090
    = surrogateDiagTailX0RatChunk001Sub000Block184Part015

theorem surrogateDiagonalTailChunk001Sub000Block184Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part015] using hcert

def TailChunk001Sub000Block184Part016SupportExplicit : Finset ℕ :=
  ([24091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24091
    = surrogateDiagTailX0RatChunk001Sub000Block184Part016

theorem surrogateDiagonalTailChunk001Sub000Block184Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part016] using hcert

def TailChunk001Sub000Block184Part017SupportExplicit : Finset ℕ :=
  ([24094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part017 : ℚ :=
  (1236339433 : ℚ) / 63027943100006400

def SurrogateDiagonalTailChunk001Sub000Block184Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24094
    = surrogateDiagTailX0RatChunk001Sub000Block184Part017

theorem surrogateDiagonalTailChunk001Sub000Block184Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part017] using hcert

def TailChunk001Sub000Block184Part018SupportExplicit : Finset ℕ :=
  ([24095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part018 : ℚ :=
  (427799423 : ℚ) / 85299745561804800

def SurrogateDiagonalTailChunk001Sub000Block184Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24095
    = surrogateDiagTailX0RatChunk001Sub000Block184Part018

theorem surrogateDiagonalTailChunk001Sub000Block184Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part018] using hcert

def TailChunk001Sub000Block184Part019SupportExplicit : Finset ℕ :=
  ([24097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24097
    = surrogateDiagTailX0RatChunk001Sub000Block184Part019

theorem surrogateDiagonalTailChunk001Sub000Block184Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part019] using hcert

def TailChunk001Sub000Block184Part020SupportExplicit : Finset ℕ :=
  ([24098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24098
    = surrogateDiagTailX0RatChunk001Sub000Block184Part020

theorem surrogateDiagonalTailChunk001Sub000Block184Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part020] using hcert

def TailChunk001Sub000Block184Part021SupportExplicit : Finset ℕ :=
  ([24099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part021 : ℚ :=
  (188842187875 : ℚ) / 142697148638833410048

def SurrogateDiagonalTailChunk001Sub000Block184Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24099
    = surrogateDiagTailX0RatChunk001Sub000Block184Part021

theorem surrogateDiagonalTailChunk001Sub000Block184Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part021] using hcert

def TailChunk001Sub000Block184Part022SupportExplicit : Finset ℕ :=
  ([24101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part022 : ℚ :=
  (7629494693 : ℚ) / 2047193893483315200

def SurrogateDiagonalTailChunk001Sub000Block184Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24101
    = surrogateDiagTailX0RatChunk001Sub000Block184Part022

theorem surrogateDiagonalTailChunk001Sub000Block184Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part022] using hcert

def TailChunk001Sub000Block184Part023SupportExplicit : Finset ℕ :=
  ([24103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block184Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24103
    = surrogateDiagTailX0RatChunk001Sub000Block184Part023

theorem surrogateDiagonalTailChunk001Sub000Block184Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part023] using hcert

def TailChunk001Sub000Block184Part024SupportExplicit : Finset ℕ :=
  ([24105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block184Part024 : ℚ :=
  (121238398925 : ℚ) / 8516849709266866176

def SurrogateDiagonalTailChunk001Sub000Block184Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24105
    = surrogateDiagTailX0RatChunk001Sub000Block184Part024

theorem surrogateDiagonalTailChunk001Sub000Block184Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block184Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block184Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block184Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block184Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block184Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block184HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block184Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block184Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block184Part000
    + surrogateDiagTailX0RatChunk001Sub000Block184Part001
    + surrogateDiagTailX0RatChunk001Sub000Block184Part002
    + surrogateDiagTailX0RatChunk001Sub000Block184Part003
    + surrogateDiagTailX0RatChunk001Sub000Block184Part004
    + surrogateDiagTailX0RatChunk001Sub000Block184Part005
    + surrogateDiagTailX0RatChunk001Sub000Block184Part006
    + surrogateDiagTailX0RatChunk001Sub000Block184Part007
    + surrogateDiagTailX0RatChunk001Sub000Block184Part008
    + surrogateDiagTailX0RatChunk001Sub000Block184Part009

def surrogateDiagonalTailChunk001Sub000Block184MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block184Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block184Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block184Part010
    + surrogateDiagTailX0RatChunk001Sub000Block184Part011
    + surrogateDiagTailX0RatChunk001Sub000Block184Part012
    + surrogateDiagTailX0RatChunk001Sub000Block184Part013
    + surrogateDiagTailX0RatChunk001Sub000Block184Part014
    + surrogateDiagTailX0RatChunk001Sub000Block184Part015
    + surrogateDiagTailX0RatChunk001Sub000Block184Part016
    + surrogateDiagTailX0RatChunk001Sub000Block184Part017
    + surrogateDiagTailX0RatChunk001Sub000Block184Part018
    + surrogateDiagTailX0RatChunk001Sub000Block184Part019

def surrogateDiagonalTailChunk001Sub000Block184TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block184Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block184Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block184Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block184Part020
    + surrogateDiagTailX0RatChunk001Sub000Block184Part021
    + surrogateDiagTailX0RatChunk001Sub000Block184Part022
    + surrogateDiagTailX0RatChunk001Sub000Block184Part023
    + surrogateDiagTailX0RatChunk001Sub000Block184Part024

def surrogateDiagonalTailChunk001Sub000Block184Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block184HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block184MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block184TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block184 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block184Part000
    + surrogateDiagTailX0RatChunk001Sub000Block184Part001
    + surrogateDiagTailX0RatChunk001Sub000Block184Part002
    + surrogateDiagTailX0RatChunk001Sub000Block184Part003
    + surrogateDiagTailX0RatChunk001Sub000Block184Part004
    + surrogateDiagTailX0RatChunk001Sub000Block184Part005
    + surrogateDiagTailX0RatChunk001Sub000Block184Part006
    + surrogateDiagTailX0RatChunk001Sub000Block184Part007
    + surrogateDiagTailX0RatChunk001Sub000Block184Part008
    + surrogateDiagTailX0RatChunk001Sub000Block184Part009
    + surrogateDiagTailX0RatChunk001Sub000Block184Part010
    + surrogateDiagTailX0RatChunk001Sub000Block184Part011
    + surrogateDiagTailX0RatChunk001Sub000Block184Part012
    + surrogateDiagTailX0RatChunk001Sub000Block184Part013
    + surrogateDiagTailX0RatChunk001Sub000Block184Part014
    + surrogateDiagTailX0RatChunk001Sub000Block184Part015
    + surrogateDiagTailX0RatChunk001Sub000Block184Part016
    + surrogateDiagTailX0RatChunk001Sub000Block184Part017
    + surrogateDiagTailX0RatChunk001Sub000Block184Part018
    + surrogateDiagTailX0RatChunk001Sub000Block184Part019
    + surrogateDiagTailX0RatChunk001Sub000Block184Part020
    + surrogateDiagTailX0RatChunk001Sub000Block184Part021
    + surrogateDiagTailX0RatChunk001Sub000Block184Part022
    + surrogateDiagTailX0RatChunk001Sub000Block184Part023
    + surrogateDiagTailX0RatChunk001Sub000Block184Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block184_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block184Head + surrogateDiagTailX0RatChunk001Sub000Block184Mid + surrogateDiagTailX0RatChunk001Sub000Block184Tail =
      surrogateDiagTailX0RatChunk001Sub000Block184 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block184Head surrogateDiagTailX0RatChunk001Sub000Block184Mid surrogateDiagTailX0RatChunk001Sub000Block184Tail surrogateDiagTailX0RatChunk001Sub000Block184
  ring

def SurrogateDiagonalTailChunk001Sub000Block184HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block184HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block184Head

def SurrogateDiagonalTailChunk001Sub000Block184MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block184MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block184Mid

def SurrogateDiagonalTailChunk001Sub000Block184TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block184TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block184Tail

theorem surrogateDiagonalTailChunk001Sub000Block184_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block184HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block184MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block184TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block184Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block184 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block184HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block184MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block184TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block184Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block184_eq_head_add_mid_add_tail

/-- Block 185 covers tail-support indices [14625,14650) and q from 24106 to 24143. -/

def TailChunk001Sub000Block185Part000SupportExplicit : Finset ℕ :=
  ([24106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part000 : ℚ :=
  (112019045075 : ℚ) / 20587794498808971264

def SurrogateDiagonalTailChunk001Sub000Block185Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24106
    = surrogateDiagTailX0RatChunk001Sub000Block185Part000

theorem surrogateDiagonalTailChunk001Sub000Block185Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part000] using hcert

def TailChunk001Sub000Block185Part001SupportExplicit : Finset ℕ :=
  ([24107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24107
    = surrogateDiagTailX0RatChunk001Sub000Block185Part001

theorem surrogateDiagonalTailChunk001Sub000Block185Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part001] using hcert

def TailChunk001Sub000Block185Part002SupportExplicit : Finset ℕ :=
  ([24109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24109
    = surrogateDiagTailX0RatChunk001Sub000Block185Part002

theorem surrogateDiagonalTailChunk001Sub000Block185Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part002] using hcert

def TailChunk001Sub000Block185Part003SupportExplicit : Finset ℕ :=
  ([24110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part003 : ℚ :=
  (29084707969 : ℚ) / 863763773827123200

def SurrogateDiagonalTailChunk001Sub000Block185Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24110
    = surrogateDiagTailX0RatChunk001Sub000Block185Part003

theorem surrogateDiagonalTailChunk001Sub000Block185Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part003] using hcert

def TailChunk001Sub000Block185Part004SupportExplicit : Finset ℕ :=
  ([24113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24113
    = surrogateDiagTailX0RatChunk001Sub000Block185Part004

theorem surrogateDiagonalTailChunk001Sub000Block185Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part004] using hcert

def TailChunk001Sub000Block185Part005SupportExplicit : Finset ℕ :=
  ([24114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part005 : ℚ :=
  (72117524075 : ℚ) / 744832357875598272

def SurrogateDiagonalTailChunk001Sub000Block185Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24114
    = surrogateDiagTailX0RatChunk001Sub000Block185Part005

theorem surrogateDiagonalTailChunk001Sub000Block185Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part005] using hcert

def TailChunk001Sub000Block185Part006SupportExplicit : Finset ℕ :=
  ([24115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part006 : ℚ :=
  (34821177875 : ℚ) / 2329251718807683072

def SurrogateDiagonalTailChunk001Sub000Block185Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24115
    = surrogateDiagTailX0RatChunk001Sub000Block185Part006

theorem surrogateDiagonalTailChunk001Sub000Block185Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part006] using hcert

def TailChunk001Sub000Block185Part007SupportExplicit : Finset ℕ :=
  ([24117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part007 : ℚ :=
  (125025 : ℚ) / 33395042031913088

def SurrogateDiagonalTailChunk001Sub000Block185Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24117
    = surrogateDiagTailX0RatChunk001Sub000Block185Part007

theorem surrogateDiagonalTailChunk001Sub000Block185Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part007] using hcert

def TailChunk001Sub000Block185Part008SupportExplicit : Finset ℕ :=
  ([24118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part008 : ℚ :=
  (1051062959 : ℚ) / 367222063890032640

def SurrogateDiagonalTailChunk001Sub000Block185Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24118
    = surrogateDiagTailX0RatChunk001Sub000Block185Part008

theorem surrogateDiagonalTailChunk001Sub000Block185Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part008] using hcert

def TailChunk001Sub000Block185Part009SupportExplicit : Finset ℕ :=
  ([24119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part009 : ℚ :=
  (487218113 : ℚ) / 3541849359490252800

def SurrogateDiagonalTailChunk001Sub000Block185Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24119
    = surrogateDiagTailX0RatChunk001Sub000Block185Part009

theorem surrogateDiagonalTailChunk001Sub000Block185Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part009] using hcert

def TailChunk001Sub000Block185Part010SupportExplicit : Finset ℕ :=
  ([24121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24121
    = surrogateDiagTailX0RatChunk001Sub000Block185Part010

theorem surrogateDiagonalTailChunk001Sub000Block185Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part010] using hcert

def TailChunk001Sub000Block185Part011SupportExplicit : Finset ℕ :=
  ([24122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part011 : ℚ :=
  (210749425 : ℚ) / 10768980958158528

def SurrogateDiagonalTailChunk001Sub000Block185Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24122
    = surrogateDiagTailX0RatChunk001Sub000Block185Part011

theorem surrogateDiagonalTailChunk001Sub000Block185Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part011] using hcert

def TailChunk001Sub000Block185Part012SupportExplicit : Finset ℕ :=
  ([24123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part012 : ℚ :=
  (3482628259 : ℚ) / 362611368316108800

def SurrogateDiagonalTailChunk001Sub000Block185Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24123
    = surrogateDiagTailX0RatChunk001Sub000Block185Part012

theorem surrogateDiagonalTailChunk001Sub000Block185Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part012] using hcert

def TailChunk001Sub000Block185Part013SupportExplicit : Finset ℕ :=
  ([24126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part013 : ℚ :=
  (1010650087 : ℚ) / 10448430394625280

def SurrogateDiagonalTailChunk001Sub000Block185Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24126
    = surrogateDiagTailX0RatChunk001Sub000Block185Part013

theorem surrogateDiagonalTailChunk001Sub000Block185Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part013] using hcert

def TailChunk001Sub000Block185Part014SupportExplicit : Finset ℕ :=
  ([24127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part014 : ℚ :=
  (116603462925 : ℚ) / 235527410921727164416

def SurrogateDiagonalTailChunk001Sub000Block185Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24127
    = surrogateDiagTailX0RatChunk001Sub000Block185Part014

theorem surrogateDiagonalTailChunk001Sub000Block185Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part014] using hcert

def TailChunk001Sub000Block185Part015SupportExplicit : Finset ℕ :=
  ([24130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part015 : ℚ :=
  (205220639425 : ℚ) / 4234274740487135232

def SurrogateDiagonalTailChunk001Sub000Block185Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24130
    = surrogateDiagTailX0RatChunk001Sub000Block185Part015

theorem surrogateDiagonalTailChunk001Sub000Block185Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part015] using hcert

def TailChunk001Sub000Block185Part016SupportExplicit : Finset ℕ :=
  ([24131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part016 : ℚ :=
  (35687882275 : ℚ) / 196028625228050276352

def SurrogateDiagonalTailChunk001Sub000Block185Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24131
    = surrogateDiagTailX0RatChunk001Sub000Block185Part016

theorem surrogateDiagonalTailChunk001Sub000Block185Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part016] using hcert

def TailChunk001Sub000Block185Part017SupportExplicit : Finset ℕ :=
  ([24133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24133
    = surrogateDiagTailX0RatChunk001Sub000Block185Part017

theorem surrogateDiagonalTailChunk001Sub000Block185Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part017] using hcert

def TailChunk001Sub000Block185Part018SupportExplicit : Finset ℕ :=
  ([24134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part018 : ℚ :=
  (37820665 : ℚ) / 3608021156579328

def SurrogateDiagonalTailChunk001Sub000Block185Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24134
    = surrogateDiagTailX0RatChunk001Sub000Block185Part018

theorem surrogateDiagonalTailChunk001Sub000Block185Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part018] using hcert

def TailChunk001Sub000Block185Part019SupportExplicit : Finset ℕ :=
  ([24135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part019 : ℚ :=
  (243079543375 : ℚ) / 17118708358554058752

def SurrogateDiagonalTailChunk001Sub000Block185Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24135
    = surrogateDiagTailX0RatChunk001Sub000Block185Part019

theorem surrogateDiagonalTailChunk001Sub000Block185Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part019] using hcert

def TailChunk001Sub000Block185Part020SupportExplicit : Finset ℕ :=
  ([24137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24137
    = surrogateDiagTailX0RatChunk001Sub000Block185Part020

theorem surrogateDiagonalTailChunk001Sub000Block185Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part020] using hcert

def TailChunk001Sub000Block185Part021SupportExplicit : Finset ℕ :=
  ([24139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part021 : ℚ :=
  (816737357 : ℚ) / 6418368889094400000

def SurrogateDiagonalTailChunk001Sub000Block185Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24139
    = surrogateDiagTailX0RatChunk001Sub000Block185Part021

theorem surrogateDiagonalTailChunk001Sub000Block185Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part021] using hcert

def TailChunk001Sub000Block185Part022SupportExplicit : Finset ℕ :=
  ([24141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part022 : ℚ :=
  (37969940125 : ℚ) / 13445693795114975232

def SurrogateDiagonalTailChunk001Sub000Block185Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24141
    = surrogateDiagTailX0RatChunk001Sub000Block185Part022

theorem surrogateDiagonalTailChunk001Sub000Block185Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part022] using hcert

def TailChunk001Sub000Block185Part023SupportExplicit : Finset ℕ :=
  ([24142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block185Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24142
    = surrogateDiagTailX0RatChunk001Sub000Block185Part023

theorem surrogateDiagonalTailChunk001Sub000Block185Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part023] using hcert

def TailChunk001Sub000Block185Part024SupportExplicit : Finset ℕ :=
  ([24143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block185Part024 : ℚ :=
  (743832821075 : ℚ) / 229018672711004995584

def SurrogateDiagonalTailChunk001Sub000Block185Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24143
    = surrogateDiagTailX0RatChunk001Sub000Block185Part024

theorem surrogateDiagonalTailChunk001Sub000Block185Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block185Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block185Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block185Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block185Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block185Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block185HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block185Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block185Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block185Part000
    + surrogateDiagTailX0RatChunk001Sub000Block185Part001
    + surrogateDiagTailX0RatChunk001Sub000Block185Part002
    + surrogateDiagTailX0RatChunk001Sub000Block185Part003
    + surrogateDiagTailX0RatChunk001Sub000Block185Part004
    + surrogateDiagTailX0RatChunk001Sub000Block185Part005
    + surrogateDiagTailX0RatChunk001Sub000Block185Part006
    + surrogateDiagTailX0RatChunk001Sub000Block185Part007
    + surrogateDiagTailX0RatChunk001Sub000Block185Part008
    + surrogateDiagTailX0RatChunk001Sub000Block185Part009

def surrogateDiagonalTailChunk001Sub000Block185MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block185Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block185Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block185Part010
    + surrogateDiagTailX0RatChunk001Sub000Block185Part011
    + surrogateDiagTailX0RatChunk001Sub000Block185Part012
    + surrogateDiagTailX0RatChunk001Sub000Block185Part013
    + surrogateDiagTailX0RatChunk001Sub000Block185Part014
    + surrogateDiagTailX0RatChunk001Sub000Block185Part015
    + surrogateDiagTailX0RatChunk001Sub000Block185Part016
    + surrogateDiagTailX0RatChunk001Sub000Block185Part017
    + surrogateDiagTailX0RatChunk001Sub000Block185Part018
    + surrogateDiagTailX0RatChunk001Sub000Block185Part019

def surrogateDiagonalTailChunk001Sub000Block185TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block185Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block185Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block185Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block185Part020
    + surrogateDiagTailX0RatChunk001Sub000Block185Part021
    + surrogateDiagTailX0RatChunk001Sub000Block185Part022
    + surrogateDiagTailX0RatChunk001Sub000Block185Part023
    + surrogateDiagTailX0RatChunk001Sub000Block185Part024

def surrogateDiagonalTailChunk001Sub000Block185Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block185HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block185MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block185TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block185 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block185Part000
    + surrogateDiagTailX0RatChunk001Sub000Block185Part001
    + surrogateDiagTailX0RatChunk001Sub000Block185Part002
    + surrogateDiagTailX0RatChunk001Sub000Block185Part003
    + surrogateDiagTailX0RatChunk001Sub000Block185Part004
    + surrogateDiagTailX0RatChunk001Sub000Block185Part005
    + surrogateDiagTailX0RatChunk001Sub000Block185Part006
    + surrogateDiagTailX0RatChunk001Sub000Block185Part007
    + surrogateDiagTailX0RatChunk001Sub000Block185Part008
    + surrogateDiagTailX0RatChunk001Sub000Block185Part009
    + surrogateDiagTailX0RatChunk001Sub000Block185Part010
    + surrogateDiagTailX0RatChunk001Sub000Block185Part011
    + surrogateDiagTailX0RatChunk001Sub000Block185Part012
    + surrogateDiagTailX0RatChunk001Sub000Block185Part013
    + surrogateDiagTailX0RatChunk001Sub000Block185Part014
    + surrogateDiagTailX0RatChunk001Sub000Block185Part015
    + surrogateDiagTailX0RatChunk001Sub000Block185Part016
    + surrogateDiagTailX0RatChunk001Sub000Block185Part017
    + surrogateDiagTailX0RatChunk001Sub000Block185Part018
    + surrogateDiagTailX0RatChunk001Sub000Block185Part019
    + surrogateDiagTailX0RatChunk001Sub000Block185Part020
    + surrogateDiagTailX0RatChunk001Sub000Block185Part021
    + surrogateDiagTailX0RatChunk001Sub000Block185Part022
    + surrogateDiagTailX0RatChunk001Sub000Block185Part023
    + surrogateDiagTailX0RatChunk001Sub000Block185Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block185_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block185Head + surrogateDiagTailX0RatChunk001Sub000Block185Mid + surrogateDiagTailX0RatChunk001Sub000Block185Tail =
      surrogateDiagTailX0RatChunk001Sub000Block185 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block185Head surrogateDiagTailX0RatChunk001Sub000Block185Mid surrogateDiagTailX0RatChunk001Sub000Block185Tail surrogateDiagTailX0RatChunk001Sub000Block185
  ring

def SurrogateDiagonalTailChunk001Sub000Block185HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block185HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block185Head

def SurrogateDiagonalTailChunk001Sub000Block185MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block185MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block185Mid

def SurrogateDiagonalTailChunk001Sub000Block185TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block185TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block185Tail

theorem surrogateDiagonalTailChunk001Sub000Block185_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block185HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block185MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block185TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block185Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block185 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block185HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block185MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block185TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block185Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block185_eq_head_add_mid_add_tail

/-- Block 186 covers tail-support indices [14650,14675) and q from 24145 to 24189. -/

def TailChunk001Sub000Block186Part000SupportExplicit : Finset ℕ :=
  ([24145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part000 : ℚ :=
  (7531546177 : ℚ) / 942373917697720320

def SurrogateDiagonalTailChunk001Sub000Block186Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24145
    = surrogateDiagTailX0RatChunk001Sub000Block186Part000

theorem surrogateDiagonalTailChunk001Sub000Block186Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part000] using hcert

def TailChunk001Sub000Block186Part001SupportExplicit : Finset ℕ :=
  ([24146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block186Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24146
    = surrogateDiagTailX0RatChunk001Sub000Block186Part001

theorem surrogateDiagonalTailChunk001Sub000Block186Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part001] using hcert

def TailChunk001Sub000Block186Part002SupportExplicit : Finset ℕ :=
  ([24149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part002 : ℚ :=
  (31010356351 : ℚ) / 21772176924672000000

def SurrogateDiagonalTailChunk001Sub000Block186Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24149
    = surrogateDiagTailX0RatChunk001Sub000Block186Part002

theorem surrogateDiagonalTailChunk001Sub000Block186Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part002] using hcert

def TailChunk001Sub000Block186Part003SupportExplicit : Finset ℕ :=
  ([24151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block186Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24151
    = surrogateDiagTailX0RatChunk001Sub000Block186Part003

theorem surrogateDiagonalTailChunk001Sub000Block186Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part003] using hcert

def TailChunk001Sub000Block186Part004SupportExplicit : Finset ℕ :=
  ([24153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part004 : ℚ :=
  (110391143725 : ℚ) / 153633945267782811648

def SurrogateDiagonalTailChunk001Sub000Block186Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24153
    = surrogateDiagTailX0RatChunk001Sub000Block186Part004

theorem surrogateDiagonalTailChunk001Sub000Block186Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part004] using hcert

def TailChunk001Sub000Block186Part005SupportExplicit : Finset ℕ :=
  ([24154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part005 : ℚ :=
  (272657597125 : ℚ) / 38454197096974123008

def SurrogateDiagonalTailChunk001Sub000Block186Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24154
    = surrogateDiagTailX0RatChunk001Sub000Block186Part005

theorem surrogateDiagonalTailChunk001Sub000Block186Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part005] using hcert

def TailChunk001Sub000Block186Part006SupportExplicit : Finset ℕ :=
  ([24155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part006 : ℚ :=
  (11674454669 : ℚ) / 2787053684352215040

def SurrogateDiagonalTailChunk001Sub000Block186Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24155
    = surrogateDiagTailX0RatChunk001Sub000Block186Part006

theorem surrogateDiagonalTailChunk001Sub000Block186Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part006] using hcert

def TailChunk001Sub000Block186Part007SupportExplicit : Finset ℕ :=
  ([24158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part007 : ℚ :=
  (45934974125 : ℚ) / 24042966493371039744

def SurrogateDiagonalTailChunk001Sub000Block186Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24158
    = surrogateDiagTailX0RatChunk001Sub000Block186Part007

theorem surrogateDiagonalTailChunk001Sub000Block186Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part007] using hcert

def TailChunk001Sub000Block186Part008SupportExplicit : Finset ℕ :=
  ([24159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part008 : ℚ :=
  (41675 : ℚ) / 11209436914046976

def SurrogateDiagonalTailChunk001Sub000Block186Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24159
    = surrogateDiagTailX0RatChunk001Sub000Block186Part008

theorem surrogateDiagonalTailChunk001Sub000Block186Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part008] using hcert

def TailChunk001Sub000Block186Part009SupportExplicit : Finset ℕ :=
  ([24161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part009 : ℚ :=
  (223495039075 : ℚ) / 758974605120927203328

def SurrogateDiagonalTailChunk001Sub000Block186Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24161
    = surrogateDiagTailX0RatChunk001Sub000Block186Part009

theorem surrogateDiagonalTailChunk001Sub000Block186Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part009] using hcert

def TailChunk001Sub000Block186Part010SupportExplicit : Finset ℕ :=
  ([24162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part010 : ℚ :=
  (506833668425 : ℚ) / 5255474438170211904

def SurrogateDiagonalTailChunk001Sub000Block186Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24162
    = surrogateDiagTailX0RatChunk001Sub000Block186Part010

theorem surrogateDiagonalTailChunk001Sub000Block186Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part010] using hcert

def TailChunk001Sub000Block186Part011SupportExplicit : Finset ℕ :=
  ([24163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part011 : ℚ :=
  (4966177873 : ℚ) / 31876644235412275200

def SurrogateDiagonalTailChunk001Sub000Block186Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24163
    = surrogateDiagTailX0RatChunk001Sub000Block186Part011

theorem surrogateDiagonalTailChunk001Sub000Block186Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part011] using hcert

def TailChunk001Sub000Block186Part012SupportExplicit : Finset ℕ :=
  ([24166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part012 : ℚ :=
  (3328397 : ℚ) / 1574489828065280

def SurrogateDiagonalTailChunk001Sub000Block186Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24166
    = surrogateDiagTailX0RatChunk001Sub000Block186Part012

theorem surrogateDiagonalTailChunk001Sub000Block186Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part012] using hcert

def TailChunk001Sub000Block186Part013SupportExplicit : Finset ℕ :=
  ([24169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block186Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24169
    = surrogateDiagTailX0RatChunk001Sub000Block186Part013

theorem surrogateDiagonalTailChunk001Sub000Block186Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part013] using hcert

def TailChunk001Sub000Block186Part014SupportExplicit : Finset ℕ :=
  ([24170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part014 : ℚ :=
  (730736473525 : ℚ) / 21809943674678673408

def SurrogateDiagonalTailChunk001Sub000Block186Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24170
    = surrogateDiagTailX0RatChunk001Sub000Block186Part014

theorem surrogateDiagonalTailChunk001Sub000Block186Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part014] using hcert

def TailChunk001Sub000Block186Part015SupportExplicit : Finset ℕ :=
  ([24171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part015 : ℚ :=
  (8304105721 : ℚ) / 906866176968000000

def SurrogateDiagonalTailChunk001Sub000Block186Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24171
    = surrogateDiagTailX0RatChunk001Sub000Block186Part015

theorem surrogateDiagonalTailChunk001Sub000Block186Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part015] using hcert

def TailChunk001Sub000Block186Part016SupportExplicit : Finset ℕ :=
  ([24173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part016 : ℚ :=
  (14044823641 : ℚ) / 28479658002642000000

def SurrogateDiagonalTailChunk001Sub000Block186Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24173
    = surrogateDiagTailX0RatChunk001Sub000Block186Part016

theorem surrogateDiagonalTailChunk001Sub000Block186Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part016] using hcert

def TailChunk001Sub000Block186Part017SupportExplicit : Finset ℕ :=
  ([24177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part017 : ℚ :=
  (41675 : ℚ) / 11242885415734656

def SurrogateDiagonalTailChunk001Sub000Block186Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24177
    = surrogateDiagTailX0RatChunk001Sub000Block186Part017

theorem surrogateDiagonalTailChunk001Sub000Block186Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part017] using hcert

def TailChunk001Sub000Block186Part018SupportExplicit : Finset ℕ :=
  ([24178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part018 : ℚ :=
  (1744613641 : ℚ) / 42649872780902400

def SurrogateDiagonalTailChunk001Sub000Block186Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24178
    = surrogateDiagTailX0RatChunk001Sub000Block186Part018

theorem surrogateDiagonalTailChunk001Sub000Block186Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part018] using hcert

def TailChunk001Sub000Block186Part019SupportExplicit : Finset ℕ :=
  ([24179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block186Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24179
    = surrogateDiagTailX0RatChunk001Sub000Block186Part019

theorem surrogateDiagonalTailChunk001Sub000Block186Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part019] using hcert

def TailChunk001Sub000Block186Part020SupportExplicit : Finset ℕ :=
  ([24181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block186Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24181
    = surrogateDiagTailX0RatChunk001Sub000Block186Part020

theorem surrogateDiagonalTailChunk001Sub000Block186Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part020] using hcert

def TailChunk001Sub000Block186Part021SupportExplicit : Finset ℕ :=
  ([24182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part021 : ℚ :=
  (4267468525 : ℚ) / 3104576944533700608

def SurrogateDiagonalTailChunk001Sub000Block186Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24182
    = surrogateDiagTailX0RatChunk001Sub000Block186Part021

theorem surrogateDiagonalTailChunk001Sub000Block186Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part021] using hcert

def TailChunk001Sub000Block186Part022SupportExplicit : Finset ℕ :=
  ([24185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part022 : ℚ :=
  (2149783183 : ℚ) / 188047770456084480

def SurrogateDiagonalTailChunk001Sub000Block186Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24185
    = surrogateDiagTailX0RatChunk001Sub000Block186Part022

theorem surrogateDiagonalTailChunk001Sub000Block186Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part022] using hcert

def TailChunk001Sub000Block186Part023SupportExplicit : Finset ℕ :=
  ([24186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part023 : ℚ :=
  (57501544675 : ℚ) / 495476210551504896

def SurrogateDiagonalTailChunk001Sub000Block186Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24186
    = surrogateDiagTailX0RatChunk001Sub000Block186Part023

theorem surrogateDiagonalTailChunk001Sub000Block186Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part023] using hcert

def TailChunk001Sub000Block186Part024SupportExplicit : Finset ℕ :=
  ([24189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block186Part024 : ℚ :=
  (16328432473 : ℚ) / 4594636487164723200

def SurrogateDiagonalTailChunk001Sub000Block186Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24189
    = surrogateDiagTailX0RatChunk001Sub000Block186Part024

theorem surrogateDiagonalTailChunk001Sub000Block186Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block186Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block186Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block186Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block186Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block186Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block186HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block186Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block186Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block186Part000
    + surrogateDiagTailX0RatChunk001Sub000Block186Part001
    + surrogateDiagTailX0RatChunk001Sub000Block186Part002
    + surrogateDiagTailX0RatChunk001Sub000Block186Part003
    + surrogateDiagTailX0RatChunk001Sub000Block186Part004
    + surrogateDiagTailX0RatChunk001Sub000Block186Part005
    + surrogateDiagTailX0RatChunk001Sub000Block186Part006
    + surrogateDiagTailX0RatChunk001Sub000Block186Part007
    + surrogateDiagTailX0RatChunk001Sub000Block186Part008
    + surrogateDiagTailX0RatChunk001Sub000Block186Part009

def surrogateDiagonalTailChunk001Sub000Block186MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block186Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block186Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block186Part010
    + surrogateDiagTailX0RatChunk001Sub000Block186Part011
    + surrogateDiagTailX0RatChunk001Sub000Block186Part012
    + surrogateDiagTailX0RatChunk001Sub000Block186Part013
    + surrogateDiagTailX0RatChunk001Sub000Block186Part014
    + surrogateDiagTailX0RatChunk001Sub000Block186Part015
    + surrogateDiagTailX0RatChunk001Sub000Block186Part016
    + surrogateDiagTailX0RatChunk001Sub000Block186Part017
    + surrogateDiagTailX0RatChunk001Sub000Block186Part018
    + surrogateDiagTailX0RatChunk001Sub000Block186Part019

def surrogateDiagonalTailChunk001Sub000Block186TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block186Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block186Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block186Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block186Part020
    + surrogateDiagTailX0RatChunk001Sub000Block186Part021
    + surrogateDiagTailX0RatChunk001Sub000Block186Part022
    + surrogateDiagTailX0RatChunk001Sub000Block186Part023
    + surrogateDiagTailX0RatChunk001Sub000Block186Part024

def surrogateDiagonalTailChunk001Sub000Block186Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block186HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block186MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block186TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block186 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block186Part000
    + surrogateDiagTailX0RatChunk001Sub000Block186Part001
    + surrogateDiagTailX0RatChunk001Sub000Block186Part002
    + surrogateDiagTailX0RatChunk001Sub000Block186Part003
    + surrogateDiagTailX0RatChunk001Sub000Block186Part004
    + surrogateDiagTailX0RatChunk001Sub000Block186Part005
    + surrogateDiagTailX0RatChunk001Sub000Block186Part006
    + surrogateDiagTailX0RatChunk001Sub000Block186Part007
    + surrogateDiagTailX0RatChunk001Sub000Block186Part008
    + surrogateDiagTailX0RatChunk001Sub000Block186Part009
    + surrogateDiagTailX0RatChunk001Sub000Block186Part010
    + surrogateDiagTailX0RatChunk001Sub000Block186Part011
    + surrogateDiagTailX0RatChunk001Sub000Block186Part012
    + surrogateDiagTailX0RatChunk001Sub000Block186Part013
    + surrogateDiagTailX0RatChunk001Sub000Block186Part014
    + surrogateDiagTailX0RatChunk001Sub000Block186Part015
    + surrogateDiagTailX0RatChunk001Sub000Block186Part016
    + surrogateDiagTailX0RatChunk001Sub000Block186Part017
    + surrogateDiagTailX0RatChunk001Sub000Block186Part018
    + surrogateDiagTailX0RatChunk001Sub000Block186Part019
    + surrogateDiagTailX0RatChunk001Sub000Block186Part020
    + surrogateDiagTailX0RatChunk001Sub000Block186Part021
    + surrogateDiagTailX0RatChunk001Sub000Block186Part022
    + surrogateDiagTailX0RatChunk001Sub000Block186Part023
    + surrogateDiagTailX0RatChunk001Sub000Block186Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block186_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block186Head + surrogateDiagTailX0RatChunk001Sub000Block186Mid + surrogateDiagTailX0RatChunk001Sub000Block186Tail =
      surrogateDiagTailX0RatChunk001Sub000Block186 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block186Head surrogateDiagTailX0RatChunk001Sub000Block186Mid surrogateDiagTailX0RatChunk001Sub000Block186Tail surrogateDiagTailX0RatChunk001Sub000Block186
  ring

def SurrogateDiagonalTailChunk001Sub000Block186HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block186HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block186Head

def SurrogateDiagonalTailChunk001Sub000Block186MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block186MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block186Mid

def SurrogateDiagonalTailChunk001Sub000Block186TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block186TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block186Tail

theorem surrogateDiagonalTailChunk001Sub000Block186_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block186HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block186MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block186TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block186Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block186 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block186HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block186MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block186TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block186Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block186_eq_head_add_mid_add_tail

/-- Block 187 covers tail-support indices [14675,14700) and q from 24190 to 24229. -/

def TailChunk001Sub000Block187Part000SupportExplicit : Finset ℕ :=
  ([24190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part000 : ℚ :=
  (5286270627 : ℚ) / 123631034905395200

def SurrogateDiagonalTailChunk001Sub000Block187Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24190
    = surrogateDiagTailX0RatChunk001Sub000Block187Part000

theorem surrogateDiagonalTailChunk001Sub000Block187Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part000] using hcert

def TailChunk001Sub000Block187Part001SupportExplicit : Finset ℕ :=
  ([24191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part001 : ℚ :=
  (10666335925 : ℚ) / 18612412724549910528

def SurrogateDiagonalTailChunk001Sub000Block187Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24191
    = surrogateDiagTailX0RatChunk001Sub000Block187Part001

theorem surrogateDiagonalTailChunk001Sub000Block187Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part001] using hcert

def TailChunk001Sub000Block187Part002SupportExplicit : Finset ℕ :=
  ([24193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part002 : ℚ :=
  (13043372321 : ℚ) / 12411767040524697600

def SurrogateDiagonalTailChunk001Sub000Block187Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24193
    = surrogateDiagTailX0RatChunk001Sub000Block187Part002

theorem surrogateDiagonalTailChunk001Sub000Block187Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part002] using hcert

def TailChunk001Sub000Block187Part003SupportExplicit : Finset ℕ :=
  ([24194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24194
    = surrogateDiagTailX0RatChunk001Sub000Block187Part003

theorem surrogateDiagonalTailChunk001Sub000Block187Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part003] using hcert

def TailChunk001Sub000Block187Part004SupportExplicit : Finset ℕ :=
  ([24195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part004 : ℚ :=
  (893923276825 : ℚ) / 17289680399667167232

def SurrogateDiagonalTailChunk001Sub000Block187Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24195
    = surrogateDiagTailX0RatChunk001Sub000Block187Part004

theorem surrogateDiagonalTailChunk001Sub000Block187Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part004] using hcert

def TailChunk001Sub000Block187Part005SupportExplicit : Finset ℕ :=
  ([24197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24197
    = surrogateDiagTailX0RatChunk001Sub000Block187Part005

theorem surrogateDiagonalTailChunk001Sub000Block187Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part005] using hcert

def TailChunk001Sub000Block187Part006SupportExplicit : Finset ℕ :=
  ([24198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part006 : ℚ :=
  (1976363616325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk001Sub000Block187Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24198
    = surrogateDiagTailX0RatChunk001Sub000Block187Part006

theorem surrogateDiagonalTailChunk001Sub000Block187Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part006] using hcert

def TailChunk001Sub000Block187Part007SupportExplicit : Finset ℕ :=
  ([24199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part007 : ℚ :=
  (747284130875 : ℚ) / 231151544683519279104

def SurrogateDiagonalTailChunk001Sub000Block187Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24199
    = surrogateDiagTailX0RatChunk001Sub000Block187Part007

theorem surrogateDiagonalTailChunk001Sub000Block187Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part007] using hcert

def TailChunk001Sub000Block187Part008SupportExplicit : Finset ℕ :=
  ([24202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24202
    = surrogateDiagTailX0RatChunk001Sub000Block187Part008

theorem surrogateDiagonalTailChunk001Sub000Block187Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part008] using hcert

def TailChunk001Sub000Block187Part009SupportExplicit : Finset ℕ :=
  ([24203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24203
    = surrogateDiagTailX0RatChunk001Sub000Block187Part009

theorem surrogateDiagonalTailChunk001Sub000Block187Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part009] using hcert

def TailChunk001Sub000Block187Part010SupportExplicit : Finset ℕ :=
  ([24205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part010 : ℚ :=
  (1560785781925 : ℚ) / 310240747382965567488

def SurrogateDiagonalTailChunk001Sub000Block187Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24205
    = surrogateDiagTailX0RatChunk001Sub000Block187Part010

theorem surrogateDiagonalTailChunk001Sub000Block187Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part010] using hcert

def TailChunk001Sub000Block187Part011SupportExplicit : Finset ℕ :=
  ([24207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part011 : ℚ :=
  (508614248225 : ℚ) / 21189485545726085376

def SurrogateDiagonalTailChunk001Sub000Block187Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24207
    = surrogateDiagTailX0RatChunk001Sub000Block187Part011

theorem surrogateDiagonalTailChunk001Sub000Block187Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part011] using hcert

def TailChunk001Sub000Block187Part012SupportExplicit : Finset ℕ :=
  ([24209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part012 : ℚ :=
  (85451630375 : ℚ) / 388096107663544870464

def SurrogateDiagonalTailChunk001Sub000Block187Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24209
    = surrogateDiagTailX0RatChunk001Sub000Block187Part012

theorem surrogateDiagonalTailChunk001Sub000Block187Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part012] using hcert

def TailChunk001Sub000Block187Part013SupportExplicit : Finset ℕ :=
  ([24211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part013 : ℚ :=
  (1406437511 : ℚ) / 810499567500000000

def SurrogateDiagonalTailChunk001Sub000Block187Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24211
    = surrogateDiagTailX0RatChunk001Sub000Block187Part013

theorem surrogateDiagonalTailChunk001Sub000Block187Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part013] using hcert

def TailChunk001Sub000Block187Part014SupportExplicit : Finset ℕ :=
  ([24213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part014 : ℚ :=
  (24218704825 : ℚ) / 634160616415690752

def SurrogateDiagonalTailChunk001Sub000Block187Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24213
    = surrogateDiagTailX0RatChunk001Sub000Block187Part014

theorem surrogateDiagonalTailChunk001Sub000Block187Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part014] using hcert

def TailChunk001Sub000Block187Part015SupportExplicit : Finset ℕ :=
  ([24214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24214
    = surrogateDiagTailX0RatChunk001Sub000Block187Part015

theorem surrogateDiagonalTailChunk001Sub000Block187Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part015] using hcert

def TailChunk001Sub000Block187Part016SupportExplicit : Finset ℕ :=
  ([24215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part016 : ℚ :=
  (397012768525 : ℚ) / 74691522203971878912

def SurrogateDiagonalTailChunk001Sub000Block187Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24215
    = surrogateDiagTailX0RatChunk001Sub000Block187Part016

theorem surrogateDiagonalTailChunk001Sub000Block187Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part016] using hcert

def TailChunk001Sub000Block187Part017SupportExplicit : Finset ℕ :=
  ([24217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part017 : ℚ :=
  (1166926247 : ℚ) / 6375328847082455040

def SurrogateDiagonalTailChunk001Sub000Block187Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24217
    = surrogateDiagTailX0RatChunk001Sub000Block187Part017

theorem surrogateDiagonalTailChunk001Sub000Block187Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part017] using hcert

def TailChunk001Sub000Block187Part018SupportExplicit : Finset ℕ :=
  ([24218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24218
    = surrogateDiagTailX0RatChunk001Sub000Block187Part018

theorem surrogateDiagonalTailChunk001Sub000Block187Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part018] using hcert

def TailChunk001Sub000Block187Part019SupportExplicit : Finset ℕ :=
  ([24221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part019 : ℚ :=
  (53009543125 : ℚ) / 263498622610013945856

def SurrogateDiagonalTailChunk001Sub000Block187Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24221
    = surrogateDiagTailX0RatChunk001Sub000Block187Part019

theorem surrogateDiagonalTailChunk001Sub000Block187Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part019] using hcert

def TailChunk001Sub000Block187Part020SupportExplicit : Finset ℕ :=
  ([24222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part020 : ℚ :=
  (15050662391 : ℚ) / 57432956089559040

def SurrogateDiagonalTailChunk001Sub000Block187Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24222
    = surrogateDiagTailX0RatChunk001Sub000Block187Part020

theorem surrogateDiagonalTailChunk001Sub000Block187Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part020] using hcert

def TailChunk001Sub000Block187Part021SupportExplicit : Finset ℕ :=
  ([24223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24223
    = surrogateDiagTailX0RatChunk001Sub000Block187Part021

theorem surrogateDiagonalTailChunk001Sub000Block187Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part021] using hcert

def TailChunk001Sub000Block187Part022SupportExplicit : Finset ℕ :=
  ([24226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24226
    = surrogateDiagTailX0RatChunk001Sub000Block187Part022

theorem surrogateDiagonalTailChunk001Sub000Block187Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part022] using hcert

def TailChunk001Sub000Block187Part023SupportExplicit : Finset ℕ :=
  ([24227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part023 : ℚ :=
  (30003996913 : ℚ) / 18577884004010035200

def SurrogateDiagonalTailChunk001Sub000Block187Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24227
    = surrogateDiagTailX0RatChunk001Sub000Block187Part023

theorem surrogateDiagonalTailChunk001Sub000Block187Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part023] using hcert

def TailChunk001Sub000Block187Part024SupportExplicit : Finset ℕ :=
  ([24229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block187Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block187Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24229
    = surrogateDiagTailX0RatChunk001Sub000Block187Part024

theorem surrogateDiagonalTailChunk001Sub000Block187Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block187Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block187Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block187Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block187Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block187Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block187HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block187Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block187Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block187Part000
    + surrogateDiagTailX0RatChunk001Sub000Block187Part001
    + surrogateDiagTailX0RatChunk001Sub000Block187Part002
    + surrogateDiagTailX0RatChunk001Sub000Block187Part003
    + surrogateDiagTailX0RatChunk001Sub000Block187Part004
    + surrogateDiagTailX0RatChunk001Sub000Block187Part005
    + surrogateDiagTailX0RatChunk001Sub000Block187Part006
    + surrogateDiagTailX0RatChunk001Sub000Block187Part007
    + surrogateDiagTailX0RatChunk001Sub000Block187Part008
    + surrogateDiagTailX0RatChunk001Sub000Block187Part009

def surrogateDiagonalTailChunk001Sub000Block187MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block187Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block187Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block187Part010
    + surrogateDiagTailX0RatChunk001Sub000Block187Part011
    + surrogateDiagTailX0RatChunk001Sub000Block187Part012
    + surrogateDiagTailX0RatChunk001Sub000Block187Part013
    + surrogateDiagTailX0RatChunk001Sub000Block187Part014
    + surrogateDiagTailX0RatChunk001Sub000Block187Part015
    + surrogateDiagTailX0RatChunk001Sub000Block187Part016
    + surrogateDiagTailX0RatChunk001Sub000Block187Part017
    + surrogateDiagTailX0RatChunk001Sub000Block187Part018
    + surrogateDiagTailX0RatChunk001Sub000Block187Part019

def surrogateDiagonalTailChunk001Sub000Block187TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block187Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block187Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block187Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block187Part020
    + surrogateDiagTailX0RatChunk001Sub000Block187Part021
    + surrogateDiagTailX0RatChunk001Sub000Block187Part022
    + surrogateDiagTailX0RatChunk001Sub000Block187Part023
    + surrogateDiagTailX0RatChunk001Sub000Block187Part024

def surrogateDiagonalTailChunk001Sub000Block187Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block187HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block187MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block187TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block187 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block187Part000
    + surrogateDiagTailX0RatChunk001Sub000Block187Part001
    + surrogateDiagTailX0RatChunk001Sub000Block187Part002
    + surrogateDiagTailX0RatChunk001Sub000Block187Part003
    + surrogateDiagTailX0RatChunk001Sub000Block187Part004
    + surrogateDiagTailX0RatChunk001Sub000Block187Part005
    + surrogateDiagTailX0RatChunk001Sub000Block187Part006
    + surrogateDiagTailX0RatChunk001Sub000Block187Part007
    + surrogateDiagTailX0RatChunk001Sub000Block187Part008
    + surrogateDiagTailX0RatChunk001Sub000Block187Part009
    + surrogateDiagTailX0RatChunk001Sub000Block187Part010
    + surrogateDiagTailX0RatChunk001Sub000Block187Part011
    + surrogateDiagTailX0RatChunk001Sub000Block187Part012
    + surrogateDiagTailX0RatChunk001Sub000Block187Part013
    + surrogateDiagTailX0RatChunk001Sub000Block187Part014
    + surrogateDiagTailX0RatChunk001Sub000Block187Part015
    + surrogateDiagTailX0RatChunk001Sub000Block187Part016
    + surrogateDiagTailX0RatChunk001Sub000Block187Part017
    + surrogateDiagTailX0RatChunk001Sub000Block187Part018
    + surrogateDiagTailX0RatChunk001Sub000Block187Part019
    + surrogateDiagTailX0RatChunk001Sub000Block187Part020
    + surrogateDiagTailX0RatChunk001Sub000Block187Part021
    + surrogateDiagTailX0RatChunk001Sub000Block187Part022
    + surrogateDiagTailX0RatChunk001Sub000Block187Part023
    + surrogateDiagTailX0RatChunk001Sub000Block187Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block187_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block187Head + surrogateDiagTailX0RatChunk001Sub000Block187Mid + surrogateDiagTailX0RatChunk001Sub000Block187Tail =
      surrogateDiagTailX0RatChunk001Sub000Block187 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block187Head surrogateDiagTailX0RatChunk001Sub000Block187Mid surrogateDiagTailX0RatChunk001Sub000Block187Tail surrogateDiagTailX0RatChunk001Sub000Block187
  ring

def SurrogateDiagonalTailChunk001Sub000Block187HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block187HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block187Head

def SurrogateDiagonalTailChunk001Sub000Block187MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block187MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block187Mid

def SurrogateDiagonalTailChunk001Sub000Block187TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block187TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block187Tail

theorem surrogateDiagonalTailChunk001Sub000Block187_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block187HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block187MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block187TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block187Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block187 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block187HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block187MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block187TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block187Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block187_eq_head_add_mid_add_tail

/-- Block 188 covers tail-support indices [14700,14725) and q from 24230 to 24267. -/

def TailChunk001Sub000Block188Part000SupportExplicit : Finset ℕ :=
  ([24230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part000 : ℚ :=
  (734364246025 : ℚ) / 22027407157347207168

def SurrogateDiagonalTailChunk001Sub000Block188Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24230
    = surrogateDiagTailX0RatChunk001Sub000Block188Part000

theorem surrogateDiagonalTailChunk001Sub000Block188Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part000] using hcert

def TailChunk001Sub000Block188Part001SupportExplicit : Finset ℕ :=
  ([24231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part001 : ℚ :=
  (79631824019 : ℚ) / 3023020469885337600

def SurrogateDiagonalTailChunk001Sub000Block188Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24231
    = surrogateDiagTailX0RatChunk001Sub000Block188Part001

theorem surrogateDiagonalTailChunk001Sub000Block188Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part001] using hcert

def TailChunk001Sub000Block188Part002SupportExplicit : Finset ℕ :=
  ([24233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part002 : ℚ :=
  (36476569843 : ℚ) / 23515602410462083200

def SurrogateDiagonalTailChunk001Sub000Block188Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24233
    = surrogateDiagTailX0RatChunk001Sub000Block188Part002

theorem surrogateDiagonalTailChunk001Sub000Block188Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part002] using hcert

def TailChunk001Sub000Block188Part003SupportExplicit : Finset ℕ :=
  ([24234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part003 : ℚ :=
  (1828061401225 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk001Sub000Block188Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24234
    = surrogateDiagTailX0RatChunk001Sub000Block188Part003

theorem surrogateDiagonalTailChunk001Sub000Block188Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part003] using hcert

def TailChunk001Sub000Block188Part004SupportExplicit : Finset ℕ :=
  ([24235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part004 : ℚ :=
  (62552803789 : ℚ) / 12283163360899891200

def SurrogateDiagonalTailChunk001Sub000Block188Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24235
    = surrogateDiagTailX0RatChunk001Sub000Block188Part004

theorem surrogateDiagonalTailChunk001Sub000Block188Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part004] using hcert

def TailChunk001Sub000Block188Part005SupportExplicit : Finset ℕ :=
  ([24238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block188Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24238
    = surrogateDiagTailX0RatChunk001Sub000Block188Part005

theorem surrogateDiagonalTailChunk001Sub000Block188Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part005] using hcert

def TailChunk001Sub000Block188Part006SupportExplicit : Finset ℕ :=
  ([24239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block188Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24239
    = surrogateDiagTailX0RatChunk001Sub000Block188Part006

theorem surrogateDiagonalTailChunk001Sub000Block188Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part006] using hcert

def TailChunk001Sub000Block188Part007SupportExplicit : Finset ℕ :=
  ([24241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part007 : ℚ :=
  (750965172925 : ℚ) / 465521897684305024128

def SurrogateDiagonalTailChunk001Sub000Block188Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24241
    = surrogateDiagTailX0RatChunk001Sub000Block188Part007

theorem surrogateDiagonalTailChunk001Sub000Block188Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part007] using hcert

def TailChunk001Sub000Block188Part008SupportExplicit : Finset ℕ :=
  ([24242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part008 : ℚ :=
  (329924131 : ℚ) / 22614127348285440

def SurrogateDiagonalTailChunk001Sub000Block188Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24242
    = surrogateDiagTailX0RatChunk001Sub000Block188Part008

theorem surrogateDiagonalTailChunk001Sub000Block188Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part008] using hcert

def TailChunk001Sub000Block188Part009SupportExplicit : Finset ℕ :=
  ([24243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part009 : ℚ :=
  (8162049971 : ℚ) / 341053319021199360

def SurrogateDiagonalTailChunk001Sub000Block188Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24243
    = surrogateDiagTailX0RatChunk001Sub000Block188Part009

theorem surrogateDiagonalTailChunk001Sub000Block188Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part009] using hcert

def TailChunk001Sub000Block188Part010SupportExplicit : Finset ℕ :=
  ([24245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part010 : ℚ :=
  (541289443325 : ℚ) / 84730996329981935616

def SurrogateDiagonalTailChunk001Sub000Block188Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24245
    = surrogateDiagTailX0RatChunk001Sub000Block188Part010

theorem surrogateDiagonalTailChunk001Sub000Block188Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part010] using hcert

def TailChunk001Sub000Block188Part011SupportExplicit : Finset ℕ :=
  ([24247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block188Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24247
    = surrogateDiagTailX0RatChunk001Sub000Block188Part011

theorem surrogateDiagonalTailChunk001Sub000Block188Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part011] using hcert

def TailChunk001Sub000Block188Part012SupportExplicit : Finset ℕ :=
  ([24249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part012 : ℚ :=
  (1336189163175 : ℚ) / 51628938331667562496

def SurrogateDiagonalTailChunk001Sub000Block188Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24249
    = surrogateDiagTailX0RatChunk001Sub000Block188Part012

theorem surrogateDiagonalTailChunk001Sub000Block188Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part012] using hcert

def TailChunk001Sub000Block188Part013SupportExplicit : Finset ℕ :=
  ([24251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block188Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24251
    = surrogateDiagTailX0RatChunk001Sub000Block188Part013

theorem surrogateDiagonalTailChunk001Sub000Block188Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part013] using hcert

def TailChunk001Sub000Block188Part014SupportExplicit : Finset ℕ :=
  ([24253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part014 : ℚ :=
  (117624298075 : ℚ) / 811504580589094773888

def SurrogateDiagonalTailChunk001Sub000Block188Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24253
    = surrogateDiagTailX0RatChunk001Sub000Block188Part014

theorem surrogateDiagonalTailChunk001Sub000Block188Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part014] using hcert

def TailChunk001Sub000Block188Part015SupportExplicit : Finset ℕ :=
  ([24254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part015 : ℚ :=
  (3084650167 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub000Block188Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24254
    = surrogateDiagTailX0RatChunk001Sub000Block188Part015

theorem surrogateDiagonalTailChunk001Sub000Block188Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part015] using hcert

def TailChunk001Sub000Block188Part016SupportExplicit : Finset ℕ :=
  ([24257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part016 : ℚ :=
  (51255763 : ℚ) / 432284677643599200

def SurrogateDiagonalTailChunk001Sub000Block188Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24257
    = surrogateDiagTailX0RatChunk001Sub000Block188Part016

theorem surrogateDiagonalTailChunk001Sub000Block188Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part016] using hcert

def TailChunk001Sub000Block188Part017SupportExplicit : Finset ℕ :=
  ([24258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part017 : ℚ :=
  (21410737097 : ℚ) / 153231691858329600

def SurrogateDiagonalTailChunk001Sub000Block188Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24258
    = surrogateDiagTailX0RatChunk001Sub000Block188Part017

theorem surrogateDiagonalTailChunk001Sub000Block188Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part017] using hcert

def TailChunk001Sub000Block188Part018SupportExplicit : Finset ℕ :=
  ([24259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part018 : ℚ :=
  (32176936575 : ℚ) / 56468161160594980864

def SurrogateDiagonalTailChunk001Sub000Block188Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24259
    = surrogateDiagTailX0RatChunk001Sub000Block188Part018

theorem surrogateDiagonalTailChunk001Sub000Block188Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part018] using hcert

def TailChunk001Sub000Block188Part019SupportExplicit : Finset ℕ :=
  ([24261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part019 : ℚ :=
  (2043543617675 : ℚ) / 85516869403746291264

def SurrogateDiagonalTailChunk001Sub000Block188Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24261
    = surrogateDiagTailX0RatChunk001Sub000Block188Part019

theorem surrogateDiagonalTailChunk001Sub000Block188Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part019] using hcert

def TailChunk001Sub000Block188Part020SupportExplicit : Finset ℕ :=
  ([24262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part020 : ℚ :=
  (31339813225 : ℚ) / 1620133887560795136

def SurrogateDiagonalTailChunk001Sub000Block188Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24262
    = surrogateDiagTailX0RatChunk001Sub000Block188Part020

theorem surrogateDiagonalTailChunk001Sub000Block188Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part020] using hcert

def TailChunk001Sub000Block188Part021SupportExplicit : Finset ℕ :=
  ([24263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part021 : ℚ :=
  (412422522925 : ℚ) / 695856321341562636288

def SurrogateDiagonalTailChunk001Sub000Block188Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24263
    = surrogateDiagTailX0RatChunk001Sub000Block188Part021

theorem surrogateDiagonalTailChunk001Sub000Block188Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part021] using hcert

def TailChunk001Sub000Block188Part022SupportExplicit : Finset ℕ :=
  ([24265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part022 : ℚ :=
  (4079560237 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk001Sub000Block188Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24265
    = surrogateDiagTailX0RatChunk001Sub000Block188Part022

theorem surrogateDiagonalTailChunk001Sub000Block188Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part022] using hcert

def TailChunk001Sub000Block188Part023SupportExplicit : Finset ℕ :=
  ([24266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part023 : ℚ :=
  (4087282767 : ℚ) / 491690676877014400

def SurrogateDiagonalTailChunk001Sub000Block188Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24266
    = surrogateDiagTailX0RatChunk001Sub000Block188Part023

theorem surrogateDiagonalTailChunk001Sub000Block188Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part023] using hcert

def TailChunk001Sub000Block188Part024SupportExplicit : Finset ℕ :=
  ([24267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block188Part024 : ℚ :=
  (1022277246325 : ℚ) / 42800754069861507072

def SurrogateDiagonalTailChunk001Sub000Block188Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24267
    = surrogateDiagTailX0RatChunk001Sub000Block188Part024

theorem surrogateDiagonalTailChunk001Sub000Block188Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block188Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block188Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block188Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block188Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block188Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block188HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block188Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block188Part000
    + surrogateDiagTailX0RatChunk001Sub000Block188Part001
    + surrogateDiagTailX0RatChunk001Sub000Block188Part002
    + surrogateDiagTailX0RatChunk001Sub000Block188Part003
    + surrogateDiagTailX0RatChunk001Sub000Block188Part004
    + surrogateDiagTailX0RatChunk001Sub000Block188Part005
    + surrogateDiagTailX0RatChunk001Sub000Block188Part006
    + surrogateDiagTailX0RatChunk001Sub000Block188Part007
    + surrogateDiagTailX0RatChunk001Sub000Block188Part008
    + surrogateDiagTailX0RatChunk001Sub000Block188Part009

def surrogateDiagonalTailChunk001Sub000Block188MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block188Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block188Part010
    + surrogateDiagTailX0RatChunk001Sub000Block188Part011
    + surrogateDiagTailX0RatChunk001Sub000Block188Part012
    + surrogateDiagTailX0RatChunk001Sub000Block188Part013
    + surrogateDiagTailX0RatChunk001Sub000Block188Part014
    + surrogateDiagTailX0RatChunk001Sub000Block188Part015
    + surrogateDiagTailX0RatChunk001Sub000Block188Part016
    + surrogateDiagTailX0RatChunk001Sub000Block188Part017
    + surrogateDiagTailX0RatChunk001Sub000Block188Part018
    + surrogateDiagTailX0RatChunk001Sub000Block188Part019

def surrogateDiagonalTailChunk001Sub000Block188TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block188Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block188Part020
    + surrogateDiagTailX0RatChunk001Sub000Block188Part021
    + surrogateDiagTailX0RatChunk001Sub000Block188Part022
    + surrogateDiagTailX0RatChunk001Sub000Block188Part023
    + surrogateDiagTailX0RatChunk001Sub000Block188Part024

def surrogateDiagonalTailChunk001Sub000Block188Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block188HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block188MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block188TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block188 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block188Part000
    + surrogateDiagTailX0RatChunk001Sub000Block188Part001
    + surrogateDiagTailX0RatChunk001Sub000Block188Part002
    + surrogateDiagTailX0RatChunk001Sub000Block188Part003
    + surrogateDiagTailX0RatChunk001Sub000Block188Part004
    + surrogateDiagTailX0RatChunk001Sub000Block188Part005
    + surrogateDiagTailX0RatChunk001Sub000Block188Part006
    + surrogateDiagTailX0RatChunk001Sub000Block188Part007
    + surrogateDiagTailX0RatChunk001Sub000Block188Part008
    + surrogateDiagTailX0RatChunk001Sub000Block188Part009
    + surrogateDiagTailX0RatChunk001Sub000Block188Part010
    + surrogateDiagTailX0RatChunk001Sub000Block188Part011
    + surrogateDiagTailX0RatChunk001Sub000Block188Part012
    + surrogateDiagTailX0RatChunk001Sub000Block188Part013
    + surrogateDiagTailX0RatChunk001Sub000Block188Part014
    + surrogateDiagTailX0RatChunk001Sub000Block188Part015
    + surrogateDiagTailX0RatChunk001Sub000Block188Part016
    + surrogateDiagTailX0RatChunk001Sub000Block188Part017
    + surrogateDiagTailX0RatChunk001Sub000Block188Part018
    + surrogateDiagTailX0RatChunk001Sub000Block188Part019
    + surrogateDiagTailX0RatChunk001Sub000Block188Part020
    + surrogateDiagTailX0RatChunk001Sub000Block188Part021
    + surrogateDiagTailX0RatChunk001Sub000Block188Part022
    + surrogateDiagTailX0RatChunk001Sub000Block188Part023
    + surrogateDiagTailX0RatChunk001Sub000Block188Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block188_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block188Head + surrogateDiagTailX0RatChunk001Sub000Block188Mid + surrogateDiagTailX0RatChunk001Sub000Block188Tail =
      surrogateDiagTailX0RatChunk001Sub000Block188 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block188Head surrogateDiagTailX0RatChunk001Sub000Block188Mid surrogateDiagTailX0RatChunk001Sub000Block188Tail surrogateDiagTailX0RatChunk001Sub000Block188
  ring

def SurrogateDiagonalTailChunk001Sub000Block188HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block188HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block188Head

def SurrogateDiagonalTailChunk001Sub000Block188MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block188MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block188Mid

def SurrogateDiagonalTailChunk001Sub000Block188TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block188TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block188Tail

theorem surrogateDiagonalTailChunk001Sub000Block188_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block188HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block188MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block188TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block188Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block188 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block188HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block188MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block188TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block188Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block188_eq_head_add_mid_add_tail

/-- Block 189 covers tail-support indices [14725,14750) and q from 24269 to 24307. -/

def TailChunk001Sub000Block189Part000SupportExplicit : Finset ℕ :=
  ([24269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part000 : ℚ :=
  (752697173125 : ℚ) / 467677088054556697728

def SurrogateDiagonalTailChunk001Sub000Block189Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24269
    = surrogateDiagTailX0RatChunk001Sub000Block189Part000

theorem surrogateDiagonalTailChunk001Sub000Block189Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part000] using hcert

def TailChunk001Sub000Block189Part001SupportExplicit : Finset ℕ :=
  ([24270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part001 : ℚ :=
  (368074587825 : ℚ) / 1455160827823783936

def SurrogateDiagonalTailChunk001Sub000Block189Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24270
    = surrogateDiagTailX0RatChunk001Sub000Block189Part001

theorem surrogateDiagonalTailChunk001Sub000Block189Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part001] using hcert

def TailChunk001Sub000Block189Part002SupportExplicit : Finset ℕ :=
  ([24271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part002 : ℚ :=
  (82044835775 : ℚ) / 78579346683656653056

def SurrogateDiagonalTailChunk001Sub000Block189Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24271
    = surrogateDiagTailX0RatChunk001Sub000Block189Part002

theorem surrogateDiagonalTailChunk001Sub000Block189Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part002] using hcert

def TailChunk001Sub000Block189Part003SupportExplicit : Finset ℕ :=
  ([24274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part003 : ℚ :=
  (43767126425 : ℚ) / 24702995869688807424

def SurrogateDiagonalTailChunk001Sub000Block189Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24274
    = surrogateDiagTailX0RatChunk001Sub000Block189Part003

theorem surrogateDiagonalTailChunk001Sub000Block189Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part003] using hcert

def TailChunk001Sub000Block189Part004SupportExplicit : Finset ℕ :=
  ([24277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part004 : ℚ :=
  (1528276381 : ℚ) / 1480433486372776200

def SurrogateDiagonalTailChunk001Sub000Block189Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24277
    = surrogateDiagTailX0RatChunk001Sub000Block189Part004

theorem surrogateDiagonalTailChunk001Sub000Block189Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part004] using hcert

def TailChunk001Sub000Block189Part005SupportExplicit : Finset ℕ :=
  ([24278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part005 : ℚ :=
  (3188744809 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk001Sub000Block189Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24278
    = surrogateDiagTailX0RatChunk001Sub000Block189Part005

theorem surrogateDiagonalTailChunk001Sub000Block189Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part005] using hcert

def TailChunk001Sub000Block189Part006SupportExplicit : Finset ℕ :=
  ([24279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part006 : ℚ :=
  (5220859675 : ℚ) / 218803505300429952

def SurrogateDiagonalTailChunk001Sub000Block189Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24279
    = surrogateDiagTailX0RatChunk001Sub000Block189Part006

theorem surrogateDiagonalTailChunk001Sub000Block189Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part006] using hcert

def TailChunk001Sub000Block189Part007SupportExplicit : Finset ℕ :=
  ([24281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block189Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24281
    = surrogateDiagTailX0RatChunk001Sub000Block189Part007

theorem surrogateDiagonalTailChunk001Sub000Block189Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part007] using hcert

def TailChunk001Sub000Block189Part008SupportExplicit : Finset ℕ :=
  ([24283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part008 : ℚ :=
  (753563923225 : ℚ) / 468757485151386421248

def SurrogateDiagonalTailChunk001Sub000Block189Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24283
    = surrogateDiagTailX0RatChunk001Sub000Block189Part008

theorem surrogateDiagonalTailChunk001Sub000Block189Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part008] using hcert

def TailChunk001Sub000Block189Part009SupportExplicit : Finset ℕ :=
  ([24285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part009 : ℚ :=
  (143266444875 : ℚ) / 2924755957329047552

def SurrogateDiagonalTailChunk001Sub000Block189Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24285
    = surrogateDiagTailX0RatChunk001Sub000Block189Part009

theorem surrogateDiagonalTailChunk001Sub000Block189Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part009] using hcert

def TailChunk001Sub000Block189Part010SupportExplicit : Finset ℕ :=
  ([24286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block189Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24286
    = surrogateDiagTailX0RatChunk001Sub000Block189Part010

theorem surrogateDiagonalTailChunk001Sub000Block189Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part010] using hcert

def TailChunk001Sub000Block189Part011SupportExplicit : Finset ℕ :=
  ([24287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part011 : ℚ :=
  (507262325 : ℚ) / 4303606451904864864

def SurrogateDiagonalTailChunk001Sub000Block189Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24287
    = surrogateDiagTailX0RatChunk001Sub000Block189Part011

theorem surrogateDiagonalTailChunk001Sub000Block189Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part011] using hcert

def TailChunk001Sub000Block189Part012SupportExplicit : Finset ℕ :=
  ([24289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part012 : ℚ :=
  (17208158775 : ℚ) / 137256470239088547008

def SurrogateDiagonalTailChunk001Sub000Block189Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24289
    = surrogateDiagTailX0RatChunk001Sub000Block189Part012

theorem surrogateDiagonalTailChunk001Sub000Block189Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part012] using hcert

def TailChunk001Sub000Block189Part013SupportExplicit : Finset ℕ :=
  ([24290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part013 : ℚ :=
  (980090108875 : ℚ) / 11889845762566422528

def SurrogateDiagonalTailChunk001Sub000Block189Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24290
    = surrogateDiagTailX0RatChunk001Sub000Block189Part013

theorem surrogateDiagonalTailChunk001Sub000Block189Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part013] using hcert

def TailChunk001Sub000Block189Part014SupportExplicit : Finset ℕ :=
  ([24293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part014 : ℚ :=
  (514488916675 : ℚ) / 681427442095418769408

def SurrogateDiagonalTailChunk001Sub000Block189Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24293
    = surrogateDiagTailX0RatChunk001Sub000Block189Part014

theorem surrogateDiagonalTailChunk001Sub000Block189Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part014] using hcert

def TailChunk001Sub000Block189Part015SupportExplicit : Finset ℕ :=
  ([24294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part015 : ℚ :=
  (256192271575 : ℚ) / 2685646609721720832

def SurrogateDiagonalTailChunk001Sub000Block189Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24294
    = surrogateDiagTailX0RatChunk001Sub000Block189Part015

theorem surrogateDiagonalTailChunk001Sub000Block189Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part015] using hcert

def TailChunk001Sub000Block189Part016SupportExplicit : Finset ℕ :=
  ([24295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part016 : ℚ :=
  (32150591125 : ℚ) / 6396464537096159232

def SurrogateDiagonalTailChunk001Sub000Block189Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24295
    = surrogateDiagTailX0RatChunk001Sub000Block189Part016

theorem surrogateDiagonalTailChunk001Sub000Block189Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part016] using hcert

def TailChunk001Sub000Block189Part017SupportExplicit : Finset ℕ :=
  ([24297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part017 : ℚ :=
  (3294316869625 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk001Sub000Block189Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24297
    = surrogateDiagTailX0RatChunk001Sub000Block189Part017

theorem surrogateDiagonalTailChunk001Sub000Block189Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part017] using hcert

def TailChunk001Sub000Block189Part018SupportExplicit : Finset ℕ :=
  ([24298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block189Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24298
    = surrogateDiagTailX0RatChunk001Sub000Block189Part018

theorem surrogateDiagonalTailChunk001Sub000Block189Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part018] using hcert

def TailChunk001Sub000Block189Part019SupportExplicit : Finset ℕ :=
  ([24301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part019 : ℚ :=
  (15322176175 : ℚ) / 25934419438374651264

def SurrogateDiagonalTailChunk001Sub000Block189Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24301
    = surrogateDiagTailX0RatChunk001Sub000Block189Part019

theorem surrogateDiagonalTailChunk001Sub000Block189Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part019] using hcert

def TailChunk001Sub000Block189Part020SupportExplicit : Finset ℕ :=
  ([24302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part020 : ℚ :=
  (34871409775 : ℚ) / 11730164971653714432

def SurrogateDiagonalTailChunk001Sub000Block189Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24302
    = surrogateDiagTailX0RatChunk001Sub000Block189Part020

theorem surrogateDiagonalTailChunk001Sub000Block189Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part020] using hcert

def TailChunk001Sub000Block189Part021SupportExplicit : Finset ℕ :=
  ([24303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part021 : ℚ :=
  (820249997 : ℚ) / 34444264275360000

def SurrogateDiagonalTailChunk001Sub000Block189Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24303
    = surrogateDiagTailX0RatChunk001Sub000Block189Part021

theorem surrogateDiagonalTailChunk001Sub000Block189Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part021] using hcert

def TailChunk001Sub000Block189Part022SupportExplicit : Finset ℕ :=
  ([24305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part022 : ℚ :=
  (11819804639 : ℚ) / 2856945056055459840

def SurrogateDiagonalTailChunk001Sub000Block189Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24305
    = surrogateDiagTailX0RatChunk001Sub000Block189Part022

theorem surrogateDiagonalTailChunk001Sub000Block189Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part022] using hcert

def TailChunk001Sub000Block189Part023SupportExplicit : Finset ℕ :=
  ([24306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part023 : ℚ :=
  (820625069 : ℚ) / 8611066068840000

def SurrogateDiagonalTailChunk001Sub000Block189Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24306
    = surrogateDiagTailX0RatChunk001Sub000Block189Part023

theorem surrogateDiagonalTailChunk001Sub000Block189Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part023] using hcert

def TailChunk001Sub000Block189Part024SupportExplicit : Finset ℕ :=
  ([24307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block189Part024 : ℚ :=
  (50662838525 : ℚ) / 413146219382867026944

def SurrogateDiagonalTailChunk001Sub000Block189Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 24307
    = surrogateDiagTailX0RatChunk001Sub000Block189Part024

theorem surrogateDiagonalTailChunk001Sub000Block189Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block189Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block189Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block189Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block189Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block189Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block189HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block189Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block189Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block189Part000
    + surrogateDiagTailX0RatChunk001Sub000Block189Part001
    + surrogateDiagTailX0RatChunk001Sub000Block189Part002
    + surrogateDiagTailX0RatChunk001Sub000Block189Part003
    + surrogateDiagTailX0RatChunk001Sub000Block189Part004
    + surrogateDiagTailX0RatChunk001Sub000Block189Part005
    + surrogateDiagTailX0RatChunk001Sub000Block189Part006
    + surrogateDiagTailX0RatChunk001Sub000Block189Part007
    + surrogateDiagTailX0RatChunk001Sub000Block189Part008
    + surrogateDiagTailX0RatChunk001Sub000Block189Part009

def surrogateDiagonalTailChunk001Sub000Block189MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block189Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block189Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block189Part010
    + surrogateDiagTailX0RatChunk001Sub000Block189Part011
    + surrogateDiagTailX0RatChunk001Sub000Block189Part012
    + surrogateDiagTailX0RatChunk001Sub000Block189Part013
    + surrogateDiagTailX0RatChunk001Sub000Block189Part014
    + surrogateDiagTailX0RatChunk001Sub000Block189Part015
    + surrogateDiagTailX0RatChunk001Sub000Block189Part016
    + surrogateDiagTailX0RatChunk001Sub000Block189Part017
    + surrogateDiagTailX0RatChunk001Sub000Block189Part018
    + surrogateDiagTailX0RatChunk001Sub000Block189Part019

def surrogateDiagonalTailChunk001Sub000Block189TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block189Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block189Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block189Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block189Part020
    + surrogateDiagTailX0RatChunk001Sub000Block189Part021
    + surrogateDiagTailX0RatChunk001Sub000Block189Part022
    + surrogateDiagTailX0RatChunk001Sub000Block189Part023
    + surrogateDiagTailX0RatChunk001Sub000Block189Part024

def surrogateDiagonalTailChunk001Sub000Block189Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block189HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block189MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block189TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block189 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block189Part000
    + surrogateDiagTailX0RatChunk001Sub000Block189Part001
    + surrogateDiagTailX0RatChunk001Sub000Block189Part002
    + surrogateDiagTailX0RatChunk001Sub000Block189Part003
    + surrogateDiagTailX0RatChunk001Sub000Block189Part004
    + surrogateDiagTailX0RatChunk001Sub000Block189Part005
    + surrogateDiagTailX0RatChunk001Sub000Block189Part006
    + surrogateDiagTailX0RatChunk001Sub000Block189Part007
    + surrogateDiagTailX0RatChunk001Sub000Block189Part008
    + surrogateDiagTailX0RatChunk001Sub000Block189Part009
    + surrogateDiagTailX0RatChunk001Sub000Block189Part010
    + surrogateDiagTailX0RatChunk001Sub000Block189Part011
    + surrogateDiagTailX0RatChunk001Sub000Block189Part012
    + surrogateDiagTailX0RatChunk001Sub000Block189Part013
    + surrogateDiagTailX0RatChunk001Sub000Block189Part014
    + surrogateDiagTailX0RatChunk001Sub000Block189Part015
    + surrogateDiagTailX0RatChunk001Sub000Block189Part016
    + surrogateDiagTailX0RatChunk001Sub000Block189Part017
    + surrogateDiagTailX0RatChunk001Sub000Block189Part018
    + surrogateDiagTailX0RatChunk001Sub000Block189Part019
    + surrogateDiagTailX0RatChunk001Sub000Block189Part020
    + surrogateDiagTailX0RatChunk001Sub000Block189Part021
    + surrogateDiagTailX0RatChunk001Sub000Block189Part022
    + surrogateDiagTailX0RatChunk001Sub000Block189Part023
    + surrogateDiagTailX0RatChunk001Sub000Block189Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block189_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block189Head + surrogateDiagTailX0RatChunk001Sub000Block189Mid + surrogateDiagTailX0RatChunk001Sub000Block189Tail =
      surrogateDiagTailX0RatChunk001Sub000Block189 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block189Head surrogateDiagTailX0RatChunk001Sub000Block189Mid surrogateDiagTailX0RatChunk001Sub000Block189Tail surrogateDiagTailX0RatChunk001Sub000Block189
  ring

def SurrogateDiagonalTailChunk001Sub000Block189HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block189HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block189Head

def SurrogateDiagonalTailChunk001Sub000Block189MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block189MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block189Mid

def SurrogateDiagonalTailChunk001Sub000Block189TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block189TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block189Tail

theorem surrogateDiagonalTailChunk001Sub000Block189_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block189HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block189MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block189TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block189Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block189 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block189HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block189MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block189TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block189Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block189_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
