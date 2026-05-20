import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [167,168). -/

/-- Block 167 covers tail-support indices [4175,4200) and q from 6919 to 6963. -/

def TailChunk000Sub000Block167Part000SupportExplicit : Finset ℕ :=
  ([6919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part000 : ℚ :=
  (238787599 : ℚ) / 2038839430348800

def SurrogateDiagonalTailChunk000Sub000Block167Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6919
    = surrogateDiagTailX0RatChunk000Sub000Block167Part000

theorem surrogateDiagonalTailChunk000Sub000Block167Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part000] using hcert

def TailChunk000Sub000Block167Part001SupportExplicit : Finset ℕ :=
  ([6922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part001 : ℚ :=
  (299463025 : ℚ) / 143347870401312

def SurrogateDiagonalTailChunk000Sub000Block167Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6922
    = surrogateDiagTailX0RatChunk000Sub000Block167Part001

theorem surrogateDiagonalTailChunk000Sub000Block167Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part001] using hcert

def TailChunk000Sub000Block167Part002SupportExplicit : Finset ℕ :=
  ([6923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part002 : ℚ :=
  (27262476575 : ℚ) / 168729768097938432

def SurrogateDiagonalTailChunk000Sub000Block167Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6923
    = surrogateDiagTailX0RatChunk000Sub000Block167Part002

theorem surrogateDiagonalTailChunk000Sub000Block167Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part002] using hcert

def TailChunk000Sub000Block167Part003SupportExplicit : Finset ℕ :=
  ([6926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part003 : ℚ :=
  (187380765625 : ℚ) / 89799748781694642

def SurrogateDiagonalTailChunk000Sub000Block167Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6926
    = surrogateDiagTailX0RatChunk000Sub000Block167Part003

theorem surrogateDiagonalTailChunk000Sub000Block167Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part003] using hcert

def TailChunk000Sub000Block167Part004SupportExplicit : Finset ℕ :=
  ([6927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part004 : ℚ :=
  (333174861275 : ℚ) / 567623103410217984

def SurrogateDiagonalTailChunk000Sub000Block167Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6927
    = surrogateDiagTailX0RatChunk000Sub000Block167Part004

theorem surrogateDiagonalTailChunk000Sub000Block167Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part004] using hcert

def TailChunk000Sub000Block167Part005SupportExplicit : Finset ℕ :=
  ([6931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part005 : ℚ :=
  (235908975 : ℚ) / 14676670193062528

def SurrogateDiagonalTailChunk000Sub000Block167Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6931
    = surrogateDiagTailX0RatChunk000Sub000Block167Part005

theorem surrogateDiagonalTailChunk000Sub000Block167Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part005] using hcert

def TailChunk000Sub000Block167Part006SupportExplicit : Finset ℕ :=
  ([6933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part006 : ℚ :=
  (13350079829 : ℚ) / 22783726402113600

def SurrogateDiagonalTailChunk000Sub000Block167Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6933
    = surrogateDiagTailX0RatChunk000Sub000Block167Part006

theorem surrogateDiagonalTailChunk000Sub000Block167Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part006] using hcert

def TailChunk000Sub000Block167Part007SupportExplicit : Finset ℕ :=
  ([6934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part007 : ℚ :=
  (187813890625 : ℚ) / 90215487664845042

def SurrogateDiagonalTailChunk000Sub000Block167Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6934
    = surrogateDiagTailX0RatChunk000Sub000Block167Part007

theorem surrogateDiagonalTailChunk000Sub000Block167Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part007] using hcert

def TailChunk000Sub000Block167Part008SupportExplicit : Finset ℕ :=
  ([6935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part008 : ℚ :=
  (530597981575 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub000Block167Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6935
    = surrogateDiagTailX0RatChunk000Sub000Block167Part008

theorem surrogateDiagonalTailChunk000Sub000Block167Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part008] using hcert

def TailChunk000Sub000Block167Part009SupportExplicit : Finset ℕ :=
  ([6937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part009 : ℚ :=
  (12316419091 : ℚ) / 124518141544579200

def SurrogateDiagonalTailChunk000Sub000Block167Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6937
    = surrogateDiagTailX0RatChunk000Sub000Block167Part009

theorem surrogateDiagonalTailChunk000Sub000Block167Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part009] using hcert

def TailChunk000Sub000Block167Part010SupportExplicit : Finset ℕ :=
  ([6938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part010 : ℚ :=
  (188030640625 : ℚ) / 90423897598647072

def SurrogateDiagonalTailChunk000Sub000Block167Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6938
    = surrogateDiagTailX0RatChunk000Sub000Block167Part010

theorem surrogateDiagonalTailChunk000Sub000Block167Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part010] using hcert

def TailChunk000Sub000Block167Part011SupportExplicit : Finset ℕ :=
  ([6941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part011 : ℚ :=
  (2683982089 : ℚ) / 52520371974000000

def SurrogateDiagonalTailChunk000Sub000Block167Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6941
    = surrogateDiagTailX0RatChunk000Sub000Block167Part011

theorem surrogateDiagonalTailChunk000Sub000Block167Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part011] using hcert

def TailChunk000Sub000Block167Part012SupportExplicit : Finset ℕ :=
  ([6942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part012 : ℚ :=
  (547181433475 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub000Block167Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6942
    = surrogateDiagTailX0RatChunk000Sub000Block167Part012

theorem surrogateDiagonalTailChunk000Sub000Block167Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part012] using hcert

def TailChunk000Sub000Block167Part013SupportExplicit : Finset ℕ :=
  ([6943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part013 : ℚ :=
  (1123880951 : ℚ) / 104434414994457600

def SurrogateDiagonalTailChunk000Sub000Block167Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6943
    = surrogateDiagTailX0RatChunk000Sub000Block167Part013

theorem surrogateDiagonalTailChunk000Sub000Block167Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part013] using hcert

def TailChunk000Sub000Block167Part014SupportExplicit : Finset ℕ :=
  ([6945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part014 : ℚ :=
  (251706789275 : ℚ) / 77768452785881088

def SurrogateDiagonalTailChunk000Sub000Block167Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6945
    = surrogateDiagTailX0RatChunk000Sub000Block167Part014

theorem surrogateDiagonalTailChunk000Sub000Block167Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part014] using hcert

def TailChunk000Sub000Block167Part015SupportExplicit : Finset ℕ :=
  ([6946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part015 : ℚ :=
  (14118782323 : ℚ) / 2965395460500000

def SurrogateDiagonalTailChunk000Sub000Block167Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6946
    = surrogateDiagTailX0RatChunk000Sub000Block167Part015

theorem surrogateDiagonalTailChunk000Sub000Block167Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part015] using hcert

def TailChunk000Sub000Block167Part016SupportExplicit : Finset ℕ :=
  ([6947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part016 : ℚ :=
  (754075140625 : ℚ) / 1455144035307348882

def SurrogateDiagonalTailChunk000Sub000Block167Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6947
    = surrogateDiagTailX0RatChunk000Sub000Block167Part016

theorem surrogateDiagonalTailChunk000Sub000Block167Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part016] using hcert

def TailChunk000Sub000Block167Part017SupportExplicit : Finset ℕ :=
  ([6949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part017 : ℚ :=
  (754509390625 : ℚ) / 1456820709810545952

def SurrogateDiagonalTailChunk000Sub000Block167Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6949
    = surrogateDiagTailX0RatChunk000Sub000Block167Part017

theorem surrogateDiagonalTailChunk000Sub000Block167Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part017] using hcert

def TailChunk000Sub000Block167Part018SupportExplicit : Finset ℕ :=
  ([6951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part018 : ℚ :=
  (27984600197 : ℚ) / 12298088053785600

def SurrogateDiagonalTailChunk000Sub000Block167Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6951
    = surrogateDiagTailX0RatChunk000Sub000Block167Part018

theorem surrogateDiagonalTailChunk000Sub000Block167Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part018] using hcert

def TailChunk000Sub000Block167Part019SupportExplicit : Finset ℕ :=
  ([6953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part019 : ℚ :=
  (695838410275 : ℚ) / 1135239387081080832

def SurrogateDiagonalTailChunk000Sub000Block167Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6953
    = surrogateDiagTailX0RatChunk000Sub000Block167Part019

theorem surrogateDiagonalTailChunk000Sub000Block167Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part019] using hcert

def TailChunk000Sub000Block167Part020SupportExplicit : Finset ℕ :=
  ([6954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part020 : ℚ :=
  (6196497203 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block167Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6954
    = surrogateDiagTailX0RatChunk000Sub000Block167Part020

theorem surrogateDiagonalTailChunk000Sub000Block167Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part020] using hcert

def TailChunk000Sub000Block167Part021SupportExplicit : Finset ℕ :=
  ([6955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part021 : ℚ :=
  (1025517041375 : ℚ) / 837886655584272384

def SurrogateDiagonalTailChunk000Sub000Block167Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6955
    = surrogateDiagTailX0RatChunk000Sub000Block167Part021

theorem surrogateDiagonalTailChunk000Sub000Block167Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part021] using hcert

def TailChunk000Sub000Block167Part022SupportExplicit : Finset ℕ :=
  ([6959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part022 : ℚ :=
  (756682515625 : ℚ) / 1465225826972890962

def SurrogateDiagonalTailChunk000Sub000Block167Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6959
    = surrogateDiagTailX0RatChunk000Sub000Block167Part022

theorem surrogateDiagonalTailChunk000Sub000Block167Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part022] using hcert

def TailChunk000Sub000Block167Part023SupportExplicit : Finset ℕ :=
  ([6961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part023 : ℚ :=
  (1211388025 : ℚ) / 2347057928282112

def SurrogateDiagonalTailChunk000Sub000Block167Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6961
    = surrogateDiagTailX0RatChunk000Sub000Block167Part023

theorem surrogateDiagonalTailChunk000Sub000Block167Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part023] using hcert

def TailChunk000Sub000Block167Part024SupportExplicit : Finset ℕ :=
  ([6963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block167Part024 : ℚ :=
  (1670117359 : ℚ) / 864532872000000

def SurrogateDiagonalTailChunk000Sub000Block167Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6963
    = surrogateDiagTailX0RatChunk000Sub000Block167Part024

theorem surrogateDiagonalTailChunk000Sub000Block167Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block167Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block167Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block167Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block167Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block167Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block167HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block167Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block167Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part000
    + surrogateDiagTailX0RatChunk000Sub000Block167Part001
    + surrogateDiagTailX0RatChunk000Sub000Block167Part002
    + surrogateDiagTailX0RatChunk000Sub000Block167Part003
    + surrogateDiagTailX0RatChunk000Sub000Block167Part004
    + surrogateDiagTailX0RatChunk000Sub000Block167Part005
    + surrogateDiagTailX0RatChunk000Sub000Block167Part006
    + surrogateDiagTailX0RatChunk000Sub000Block167Part007
    + surrogateDiagTailX0RatChunk000Sub000Block167Part008
    + surrogateDiagTailX0RatChunk000Sub000Block167Part009

def surrogateDiagonalTailChunk000Sub000Block167MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block167Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block167Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part010
    + surrogateDiagTailX0RatChunk000Sub000Block167Part011
    + surrogateDiagTailX0RatChunk000Sub000Block167Part012
    + surrogateDiagTailX0RatChunk000Sub000Block167Part013
    + surrogateDiagTailX0RatChunk000Sub000Block167Part014
    + surrogateDiagTailX0RatChunk000Sub000Block167Part015
    + surrogateDiagTailX0RatChunk000Sub000Block167Part016
    + surrogateDiagTailX0RatChunk000Sub000Block167Part017
    + surrogateDiagTailX0RatChunk000Sub000Block167Part018
    + surrogateDiagTailX0RatChunk000Sub000Block167Part019

def surrogateDiagonalTailChunk000Sub000Block167TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block167Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block167Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block167Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part020
    + surrogateDiagTailX0RatChunk000Sub000Block167Part021
    + surrogateDiagTailX0RatChunk000Sub000Block167Part022
    + surrogateDiagTailX0RatChunk000Sub000Block167Part023
    + surrogateDiagTailX0RatChunk000Sub000Block167Part024

def surrogateDiagonalTailChunk000Sub000Block167Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block167HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block167MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block167TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block167 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block167Part000
    + surrogateDiagTailX0RatChunk000Sub000Block167Part001
    + surrogateDiagTailX0RatChunk000Sub000Block167Part002
    + surrogateDiagTailX0RatChunk000Sub000Block167Part003
    + surrogateDiagTailX0RatChunk000Sub000Block167Part004
    + surrogateDiagTailX0RatChunk000Sub000Block167Part005
    + surrogateDiagTailX0RatChunk000Sub000Block167Part006
    + surrogateDiagTailX0RatChunk000Sub000Block167Part007
    + surrogateDiagTailX0RatChunk000Sub000Block167Part008
    + surrogateDiagTailX0RatChunk000Sub000Block167Part009
    + surrogateDiagTailX0RatChunk000Sub000Block167Part010
    + surrogateDiagTailX0RatChunk000Sub000Block167Part011
    + surrogateDiagTailX0RatChunk000Sub000Block167Part012
    + surrogateDiagTailX0RatChunk000Sub000Block167Part013
    + surrogateDiagTailX0RatChunk000Sub000Block167Part014
    + surrogateDiagTailX0RatChunk000Sub000Block167Part015
    + surrogateDiagTailX0RatChunk000Sub000Block167Part016
    + surrogateDiagTailX0RatChunk000Sub000Block167Part017
    + surrogateDiagTailX0RatChunk000Sub000Block167Part018
    + surrogateDiagTailX0RatChunk000Sub000Block167Part019
    + surrogateDiagTailX0RatChunk000Sub000Block167Part020
    + surrogateDiagTailX0RatChunk000Sub000Block167Part021
    + surrogateDiagTailX0RatChunk000Sub000Block167Part022
    + surrogateDiagTailX0RatChunk000Sub000Block167Part023
    + surrogateDiagTailX0RatChunk000Sub000Block167Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block167_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block167Head + surrogateDiagTailX0RatChunk000Sub000Block167Mid + surrogateDiagTailX0RatChunk000Sub000Block167Tail =
      surrogateDiagTailX0RatChunk000Sub000Block167 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block167Head surrogateDiagTailX0RatChunk000Sub000Block167Mid surrogateDiagTailX0RatChunk000Sub000Block167Tail surrogateDiagTailX0RatChunk000Sub000Block167
  ring

def SurrogateDiagonalTailChunk000Sub000Block167HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block167HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block167Head

def SurrogateDiagonalTailChunk000Sub000Block167MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block167MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block167Mid

def SurrogateDiagonalTailChunk000Sub000Block167TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block167TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block167Tail

theorem surrogateDiagonalTailChunk000Sub000Block167_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block167HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block167MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block167TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block167Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block167 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block167HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block167MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block167TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block167Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block167_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
