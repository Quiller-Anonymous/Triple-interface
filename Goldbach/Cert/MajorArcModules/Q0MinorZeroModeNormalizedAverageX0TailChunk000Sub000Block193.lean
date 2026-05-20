import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [193,194). -/

/-- Block 193 covers tail-support indices [4825,4850) and q from 7989 to 8026. -/

def TailChunk000Sub000Block193Part000SupportExplicit : Finset ℕ :=
  ([7989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part000 : ℚ :=
  (553857608275 : ℚ) / 502248969983415072

def SurrogateDiagonalTailChunk000Sub000Block193Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7989
    = surrogateDiagTailX0RatChunk000Sub000Block193Part000

theorem surrogateDiagonalTailChunk000Sub000Block193Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part000] using hcert

def TailChunk000Sub000Block193Part001SupportExplicit : Finset ℕ :=
  ([7990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part001 : ℚ :=
  (817397001625 : ℚ) / 187835675729461248

def SurrogateDiagonalTailChunk000Sub000Block193Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7990
    = surrogateDiagTailX0RatChunk000Sub000Block193Part001

theorem surrogateDiagonalTailChunk000Sub000Block193Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part001] using hcert

def TailChunk000Sub000Block193Part002SupportExplicit : Finset ℕ :=
  ([7991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part002 : ℚ :=
  (51476933273 : ℚ) / 123408196704000000

def SurrogateDiagonalTailChunk000Sub000Block193Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7991
    = surrogateDiagTailX0RatChunk000Sub000Block193Part002

theorem surrogateDiagonalTailChunk000Sub000Block193Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part002] using hcert

def TailChunk000Sub000Block193Part003SupportExplicit : Finset ℕ :=
  ([7993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part003 : ℚ :=
  (998250765625 : ℚ) / 2550285304832512512

def SurrogateDiagonalTailChunk000Sub000Block193Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7993
    = surrogateDiagTailX0RatChunk000Sub000Block193Part003

theorem surrogateDiagonalTailChunk000Sub000Block193Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part003] using hcert

def TailChunk000Sub000Block193Part004SupportExplicit : Finset ℕ :=
  ([7994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part004 : ℚ :=
  (35820381613 : ℚ) / 13683313411459200

def SurrogateDiagonalTailChunk000Sub000Block193Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7994
    = surrogateDiagTailX0RatChunk000Sub000Block193Part004

theorem surrogateDiagonalTailChunk000Sub000Block193Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part004] using hcert

def TailChunk000Sub000Block193Part005SupportExplicit : Finset ℕ :=
  ([7995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part005 : ℚ :=
  (7275798953 : ℚ) / 2718452573798400

def SurrogateDiagonalTailChunk000Sub000Block193Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7995
    = surrogateDiagTailX0RatChunk000Sub000Block193Part005

theorem surrogateDiagonalTailChunk000Sub000Block193Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part005] using hcert

def TailChunk000Sub000Block193Part006SupportExplicit : Finset ℕ :=
  ([7997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part006 : ℚ :=
  (423708283 : ℚ) / 842014156357440

def SurrogateDiagonalTailChunk000Sub000Block193Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7997
    = surrogateDiagTailX0RatChunk000Sub000Block193Part006

theorem surrogateDiagonalTailChunk000Sub000Block193Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part006] using hcert

def TailChunk000Sub000Block193Part007SupportExplicit : Finset ℕ :=
  ([7998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part007 : ℚ :=
  (25561468291 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block193Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7998
    = surrogateDiagTailX0RatChunk000Sub000Block193Part007

theorem surrogateDiagonalTailChunk000Sub000Block193Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part007] using hcert

def TailChunk000Sub000Block193Part008SupportExplicit : Finset ℕ :=
  ([7999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part008 : ℚ :=
  (147984275107 : ℚ) / 326718729975859200

def SurrogateDiagonalTailChunk000Sub000Block193Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7999
    = surrogateDiagTailX0RatChunk000Sub000Block193Part008

theorem surrogateDiagonalTailChunk000Sub000Block193Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part008] using hcert

def TailChunk000Sub000Block193Part009SupportExplicit : Finset ℕ :=
  ([8002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part009 : ℚ :=
  (80023996999 : ℚ) / 25605120000000000

def SurrogateDiagonalTailChunk000Sub000Block193Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8002
    = surrogateDiagTailX0RatChunk000Sub000Block193Part009

theorem surrogateDiagonalTailChunk000Sub000Block193Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part009] using hcert

def TailChunk000Sub000Block193Part010SupportExplicit : Finset ℕ :=
  ([8003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part010 : ℚ :=
  (154574076427 : ℚ) / 370224590112000000

def SurrogateDiagonalTailChunk000Sub000Block193Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8003
    = surrogateDiagTailX0RatChunk000Sub000Block193Part010

theorem surrogateDiagonalTailChunk000Sub000Block193Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part010] using hcert

def TailChunk000Sub000Block193Part011SupportExplicit : Finset ℕ :=
  ([8005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part011 : ℚ :=
  (38422643799 : ℚ) / 55935238144000000

def SurrogateDiagonalTailChunk000Sub000Block193Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8005
    = surrogateDiagTailX0RatChunk000Sub000Block193Part011

theorem surrogateDiagonalTailChunk000Sub000Block193Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part011] using hcert

def TailChunk000Sub000Block193Part012SupportExplicit : Finset ℕ :=
  ([8006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part012 : ℚ :=
  (2002600524775 : ℚ) / 641409216512104008

def SurrogateDiagonalTailChunk000Sub000Block193Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8006
    = surrogateDiagTailX0RatChunk000Sub000Block193Part012

theorem surrogateDiagonalTailChunk000Sub000Block193Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part012] using hcert

def TailChunk000Sub000Block193Part013SupportExplicit : Finset ℕ :=
  ([8007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part013 : ℚ :=
  (2048383358725 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub000Block193Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8007
    = surrogateDiagTailX0RatChunk000Sub000Block193Part013

theorem surrogateDiagonalTailChunk000Sub000Block193Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part013] using hcert

def TailChunk000Sub000Block193Part014SupportExplicit : Finset ℕ :=
  ([8009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part014 : ℚ :=
  (1002251265625 : ℚ) / 2570769421316608512

def SurrogateDiagonalTailChunk000Sub000Block193Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8009
    = surrogateDiagTailX0RatChunk000Sub000Block193Part014

theorem surrogateDiagonalTailChunk000Sub000Block193Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part014] using hcert

def TailChunk000Sub000Block193Part015SupportExplicit : Finset ℕ :=
  ([8011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part015 : ℚ :=
  (1604403025 : ℚ) / 4117341735696402

def SurrogateDiagonalTailChunk000Sub000Block193Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8011
    = surrogateDiagTailX0RatChunk000Sub000Block193Part015

theorem surrogateDiagonalTailChunk000Sub000Block193Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part015] using hcert

def TailChunk000Sub000Block193Part016SupportExplicit : Finset ℕ :=
  ([8013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part016 : ℚ :=
  (22287625657 : ℚ) / 20332551781216800

def SurrogateDiagonalTailChunk000Sub000Block193Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8013
    = surrogateDiagTailX0RatChunk000Sub000Block193Part016

theorem surrogateDiagonalTailChunk000Sub000Block193Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part016] using hcert

def TailChunk000Sub000Block193Part017SupportExplicit : Finset ℕ :=
  ([8014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part017 : ℚ :=
  (2006604723775 : ℚ) / 643977418372968648

def SurrogateDiagonalTailChunk000Sub000Block193Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8014
    = surrogateDiagTailX0RatChunk000Sub000Block193Part017

theorem surrogateDiagonalTailChunk000Sub000Block193Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part017] using hcert

def TailChunk000Sub000Block193Part018SupportExplicit : Finset ℕ :=
  ([8015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part018 : ℚ :=
  (2483681656975 : ℚ) / 2241874069333475328

def SurrogateDiagonalTailChunk000Sub000Block193Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8015
    = surrogateDiagTailX0RatChunk000Sub000Block193Part018

theorem surrogateDiagonalTailChunk000Sub000Block193Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part018] using hcert

def TailChunk000Sub000Block193Part019SupportExplicit : Finset ℕ :=
  ([8017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block193Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8017
    = surrogateDiagTailX0RatChunk000Sub000Block193Part019

theorem surrogateDiagonalTailChunk000Sub000Block193Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part019] using hcert

def TailChunk000Sub000Block193Part020SupportExplicit : Finset ℕ :=
  ([8018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part020 : ℚ :=
  (38487901351 : ℚ) / 20419920623491200

def SurrogateDiagonalTailChunk000Sub000Block193Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8018
    = surrogateDiagTailX0RatChunk000Sub000Block193Part020

theorem surrogateDiagonalTailChunk000Sub000Block193Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part020] using hcert

def TailChunk000Sub000Block193Part021SupportExplicit : Finset ℕ :=
  ([8021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part021 : ℚ :=
  (3018978925 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub000Block193Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8021
    = surrogateDiagTailX0RatChunk000Sub000Block193Part021

theorem surrogateDiagonalTailChunk000Sub000Block193Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part021] using hcert

def TailChunk000Sub000Block193Part022SupportExplicit : Finset ℕ :=
  ([8022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part022 : ℚ :=
  (540959027 : ℚ) / 54057534465024

def SurrogateDiagonalTailChunk000Sub000Block193Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8022
    = surrogateDiagTailX0RatChunk000Sub000Block193Part022

theorem surrogateDiagonalTailChunk000Sub000Block193Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part022] using hcert

def TailChunk000Sub000Block193Part023SupportExplicit : Finset ℕ :=
  ([8023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part023 : ℚ :=
  (12963427 : ℚ) / 2159300335632384

def SurrogateDiagonalTailChunk000Sub000Block193Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8023
    = surrogateDiagTailX0RatChunk000Sub000Block193Part023

theorem surrogateDiagonalTailChunk000Sub000Block193Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part023] using hcert

def TailChunk000Sub000Block193Part024SupportExplicit : Finset ℕ :=
  ([8026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block193Part024 : ℚ :=
  (251627640625 : ℚ) / 161961043024418592

def SurrogateDiagonalTailChunk000Sub000Block193Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8026
    = surrogateDiagTailX0RatChunk000Sub000Block193Part024

theorem surrogateDiagonalTailChunk000Sub000Block193Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block193Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block193Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block193Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block193Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block193Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block193HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block193Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block193Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part000
    + surrogateDiagTailX0RatChunk000Sub000Block193Part001
    + surrogateDiagTailX0RatChunk000Sub000Block193Part002
    + surrogateDiagTailX0RatChunk000Sub000Block193Part003
    + surrogateDiagTailX0RatChunk000Sub000Block193Part004
    + surrogateDiagTailX0RatChunk000Sub000Block193Part005
    + surrogateDiagTailX0RatChunk000Sub000Block193Part006
    + surrogateDiagTailX0RatChunk000Sub000Block193Part007
    + surrogateDiagTailX0RatChunk000Sub000Block193Part008
    + surrogateDiagTailX0RatChunk000Sub000Block193Part009

def surrogateDiagonalTailChunk000Sub000Block193MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block193Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block193Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part010
    + surrogateDiagTailX0RatChunk000Sub000Block193Part011
    + surrogateDiagTailX0RatChunk000Sub000Block193Part012
    + surrogateDiagTailX0RatChunk000Sub000Block193Part013
    + surrogateDiagTailX0RatChunk000Sub000Block193Part014
    + surrogateDiagTailX0RatChunk000Sub000Block193Part015
    + surrogateDiagTailX0RatChunk000Sub000Block193Part016
    + surrogateDiagTailX0RatChunk000Sub000Block193Part017
    + surrogateDiagTailX0RatChunk000Sub000Block193Part018
    + surrogateDiagTailX0RatChunk000Sub000Block193Part019

def surrogateDiagonalTailChunk000Sub000Block193TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block193Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block193Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block193Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part020
    + surrogateDiagTailX0RatChunk000Sub000Block193Part021
    + surrogateDiagTailX0RatChunk000Sub000Block193Part022
    + surrogateDiagTailX0RatChunk000Sub000Block193Part023
    + surrogateDiagTailX0RatChunk000Sub000Block193Part024

def surrogateDiagonalTailChunk000Sub000Block193Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block193HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block193MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block193TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block193 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block193Part000
    + surrogateDiagTailX0RatChunk000Sub000Block193Part001
    + surrogateDiagTailX0RatChunk000Sub000Block193Part002
    + surrogateDiagTailX0RatChunk000Sub000Block193Part003
    + surrogateDiagTailX0RatChunk000Sub000Block193Part004
    + surrogateDiagTailX0RatChunk000Sub000Block193Part005
    + surrogateDiagTailX0RatChunk000Sub000Block193Part006
    + surrogateDiagTailX0RatChunk000Sub000Block193Part007
    + surrogateDiagTailX0RatChunk000Sub000Block193Part008
    + surrogateDiagTailX0RatChunk000Sub000Block193Part009
    + surrogateDiagTailX0RatChunk000Sub000Block193Part010
    + surrogateDiagTailX0RatChunk000Sub000Block193Part011
    + surrogateDiagTailX0RatChunk000Sub000Block193Part012
    + surrogateDiagTailX0RatChunk000Sub000Block193Part013
    + surrogateDiagTailX0RatChunk000Sub000Block193Part014
    + surrogateDiagTailX0RatChunk000Sub000Block193Part015
    + surrogateDiagTailX0RatChunk000Sub000Block193Part016
    + surrogateDiagTailX0RatChunk000Sub000Block193Part017
    + surrogateDiagTailX0RatChunk000Sub000Block193Part018
    + surrogateDiagTailX0RatChunk000Sub000Block193Part019
    + surrogateDiagTailX0RatChunk000Sub000Block193Part020
    + surrogateDiagTailX0RatChunk000Sub000Block193Part021
    + surrogateDiagTailX0RatChunk000Sub000Block193Part022
    + surrogateDiagTailX0RatChunk000Sub000Block193Part023
    + surrogateDiagTailX0RatChunk000Sub000Block193Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block193_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block193Head + surrogateDiagTailX0RatChunk000Sub000Block193Mid + surrogateDiagTailX0RatChunk000Sub000Block193Tail =
      surrogateDiagTailX0RatChunk000Sub000Block193 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block193Head surrogateDiagTailX0RatChunk000Sub000Block193Mid surrogateDiagTailX0RatChunk000Sub000Block193Tail surrogateDiagTailX0RatChunk000Sub000Block193
  ring

def SurrogateDiagonalTailChunk000Sub000Block193HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block193HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block193Head

def SurrogateDiagonalTailChunk000Sub000Block193MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block193MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block193Mid

def SurrogateDiagonalTailChunk000Sub000Block193TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block193TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block193Tail

theorem surrogateDiagonalTailChunk000Sub000Block193_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block193HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block193MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block193TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block193Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block193 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block193HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block193MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block193TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block193Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block193_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
