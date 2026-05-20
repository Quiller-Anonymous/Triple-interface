import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [188,189). -/

/-- Block 188 covers tail-support indices [4700,4725) and q from 7779 to 7817. -/

def TailChunk000Sub000Block188Part000SupportExplicit : Finset ℕ :=
  ([7779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part000 : ℚ :=
  (420132452075 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub000Block188Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7779
    = surrogateDiagTailX0RatChunk000Sub000Block188Part000

theorem surrogateDiagonalTailChunk000Sub000Block188Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part000] using hcert

def TailChunk000Sub000Block188Part001SupportExplicit : Finset ℕ :=
  ([7781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part001 : ℚ :=
  (333239707 : ℚ) / 31646953125000000

def SurrogateDiagonalTailChunk000Sub000Block188Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7781
    = surrogateDiagTailX0RatChunk000Sub000Block188Part001

theorem surrogateDiagonalTailChunk000Sub000Block188Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part001] using hcert

def TailChunk000Sub000Block188Part002SupportExplicit : Finset ℕ :=
  ([7782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part002 : ℚ :=
  (735582751225 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block188Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7782
    = surrogateDiagTailX0RatChunk000Sub000Block188Part002

theorem surrogateDiagonalTailChunk000Sub000Block188Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part002] using hcert

def TailChunk000Sub000Block188Part003SupportExplicit : Finset ℕ :=
  ([7783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part003 : ℚ :=
  (139183721 : ℚ) / 16335936498792960

def SurrogateDiagonalTailChunk000Sub000Block188Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7783
    = surrogateDiagTailX0RatChunk000Sub000Block188Part003

theorem surrogateDiagonalTailChunk000Sub000Block188Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part003] using hcert

def TailChunk000Sub000Block188Part004SupportExplicit : Finset ℕ :=
  ([7786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part004 : ℚ :=
  (905118563725 : ℚ) / 442839322337476608

def SurrogateDiagonalTailChunk000Sub000Block188Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7786
    = surrogateDiagTailX0RatChunk000Sub000Block188Part004

theorem surrogateDiagonalTailChunk000Sub000Block188Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part004] using hcert

def TailChunk000Sub000Block188Part005SupportExplicit : Finset ℕ :=
  ([7787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part005 : ℚ :=
  (15737103325 : ℚ) / 510050557644466176

def SurrogateDiagonalTailChunk000Sub000Block188Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7787
    = surrogateDiagTailX0RatChunk000Sub000Block188Part005

theorem surrogateDiagonalTailChunk000Sub000Block188Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part005] using hcert

def TailChunk000Sub000Block188Part006SupportExplicit : Finset ℕ :=
  ([7789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block188Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7789
    = surrogateDiagTailX0RatChunk000Sub000Block188Part006

theorem surrogateDiagonalTailChunk000Sub000Block188Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part006] using hcert

def TailChunk000Sub000Block188Part007SupportExplicit : Finset ℕ :=
  ([7790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part007 : ℚ :=
  (15615268223 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block188Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7790
    = surrogateDiagTailX0RatChunk000Sub000Block188Part007

theorem surrogateDiagonalTailChunk000Sub000Block188Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part007] using hcert

def TailChunk000Sub000Block188Part008SupportExplicit : Finset ℕ :=
  ([7793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block188Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7793
    = surrogateDiagTailX0RatChunk000Sub000Block188Part008

theorem surrogateDiagonalTailChunk000Sub000Block188Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part008] using hcert

def TailChunk000Sub000Block188Part009SupportExplicit : Finset ℕ :=
  ([7795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part009 : ℚ :=
  (57024867725 : ℚ) / 471461952615495936

def SurrogateDiagonalTailChunk000Sub000Block188Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7795
    = surrogateDiagTailX0RatChunk000Sub000Block188Part009

theorem surrogateDiagonalTailChunk000Sub000Block188Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part009] using hcert

def TailChunk000Sub000Block188Part010SupportExplicit : Finset ℕ :=
  ([7797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part010 : ℚ :=
  (140227976925 : ℚ) / 245786714977599488

def SurrogateDiagonalTailChunk000Sub000Block188Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7797
    = surrogateDiagTailX0RatChunk000Sub000Block188Part010

theorem surrogateDiagonalTailChunk000Sub000Block188Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part010] using hcert

def TailChunk000Sub000Block188Part011SupportExplicit : Finset ℕ :=
  ([7798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part011 : ℚ :=
  (852150657625 : ℚ) / 309692741610129408

def SurrogateDiagonalTailChunk000Sub000Block188Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7798
    = surrogateDiagTailX0RatChunk000Sub000Block188Part011

theorem surrogateDiagonalTailChunk000Sub000Block188Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part011] using hcert

def TailChunk000Sub000Block188Part012SupportExplicit : Finset ℕ :=
  ([7799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part012 : ℚ :=
  (8886661399 : ℚ) / 251315850815539200

def SurrogateDiagonalTailChunk000Sub000Block188Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7799
    = surrogateDiagTailX0RatChunk000Sub000Block188Part012

theorem surrogateDiagonalTailChunk000Sub000Block188Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part012] using hcert

def TailChunk000Sub000Block188Part013SupportExplicit : Finset ℕ :=
  ([7801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part013 : ℚ :=
  (93713558875 : ℚ) / 7928630163751600128

def SurrogateDiagonalTailChunk000Sub000Block188Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7801
    = surrogateDiagTailX0RatChunk000Sub000Block188Part013

theorem surrogateDiagonalTailChunk000Sub000Block188Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part013] using hcert

def TailChunk000Sub000Block188Part014SupportExplicit : Finset ℕ :=
  ([7802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part014 : ℚ :=
  (464201925725 : ℚ) / 253095019762496064

def SurrogateDiagonalTailChunk000Sub000Block188Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7802
    = surrogateDiagTailX0RatChunk000Sub000Block188Part014

theorem surrogateDiagonalTailChunk000Sub000Block188Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part014] using hcert

def TailChunk000Sub000Block188Part015SupportExplicit : Finset ℕ :=
  ([7805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part015 : ℚ :=
  (583392105025 : ℚ) / 2015040240855318528

def SurrogateDiagonalTailChunk000Sub000Block188Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7805
    = surrogateDiagTailX0RatChunk000Sub000Block188Part015

theorem surrogateDiagonalTailChunk000Sub000Block188Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part015] using hcert

def TailChunk000Sub000Block188Part016SupportExplicit : Finset ℕ :=
  ([7806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part016 : ℚ :=
  (29605061197 : ℚ) / 4570673952000000

def SurrogateDiagonalTailChunk000Sub000Block188Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7806
    = surrogateDiagTailX0RatChunk000Sub000Block188Part016

theorem surrogateDiagonalTailChunk000Sub000Block188Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part016] using hcert

def TailChunk000Sub000Block188Part017SupportExplicit : Finset ℕ :=
  ([7807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part017 : ℚ :=
  (114197497 : ℚ) / 12100693702809600

def SurrogateDiagonalTailChunk000Sub000Block188Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7807
    = surrogateDiagTailX0RatChunk000Sub000Block188Part017

theorem surrogateDiagonalTailChunk000Sub000Block188Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part017] using hcert

def TailChunk000Sub000Block188Part018SupportExplicit : Finset ℕ :=
  ([7809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part018 : ℚ :=
  (35092828325 : ℚ) / 59866139553103872

def SurrogateDiagonalTailChunk000Sub000Block188Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7809
    = surrogateDiagTailX0RatChunk000Sub000Block188Part018

theorem surrogateDiagonalTailChunk000Sub000Block188Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part018] using hcert

def TailChunk000Sub000Block188Part019SupportExplicit : Finset ℕ :=
  ([7810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part019 : ℚ :=
  (76557081 : ℚ) / 16009868000000

def SurrogateDiagonalTailChunk000Sub000Block188Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7810
    = surrogateDiagTailX0RatChunk000Sub000Block188Part019

theorem surrogateDiagonalTailChunk000Sub000Block188Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part019] using hcert

def TailChunk000Sub000Block188Part020SupportExplicit : Finset ℕ :=
  ([7811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part020 : ℚ :=
  (18347564275 : ℚ) / 2827867462596919296

def SurrogateDiagonalTailChunk000Sub000Block188Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7811
    = surrogateDiagTailX0RatChunk000Sub000Block188Part020

theorem surrogateDiagonalTailChunk000Sub000Block188Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part020] using hcert

def TailChunk000Sub000Block188Part021SupportExplicit : Finset ℕ :=
  ([7813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part021 : ℚ :=
  (29725319 : ℚ) / 58331664000000

def SurrogateDiagonalTailChunk000Sub000Block188Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7813
    = surrogateDiagTailX0RatChunk000Sub000Block188Part021

theorem surrogateDiagonalTailChunk000Sub000Block188Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part021] using hcert

def TailChunk000Sub000Block188Part022SupportExplicit : Finset ℕ :=
  ([7814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part022 : ℚ :=
  (1907699508775 : ℚ) / 582043997349605448

def SurrogateDiagonalTailChunk000Sub000Block188Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7814
    = surrogateDiagTailX0RatChunk000Sub000Block188Part022

theorem surrogateDiagonalTailChunk000Sub000Block188Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part022] using hcert

def TailChunk000Sub000Block188Part023SupportExplicit : Finset ℕ :=
  ([7815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part023 : ℚ :=
  (8210457461 : ℚ) / 3744296101478400

def SurrogateDiagonalTailChunk000Sub000Block188Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7815
    = surrogateDiagTailX0RatChunk000Sub000Block188Part023

theorem surrogateDiagonalTailChunk000Sub000Block188Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part023] using hcert

def TailChunk000Sub000Block188Part024SupportExplicit : Finset ℕ :=
  ([7817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block188Part024 : ℚ :=
  (954773265625 : ℚ) / 2332948062626222592

def SurrogateDiagonalTailChunk000Sub000Block188Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7817
    = surrogateDiagTailX0RatChunk000Sub000Block188Part024

theorem surrogateDiagonalTailChunk000Sub000Block188Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block188Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block188Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block188Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block188Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block188Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block188HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block188Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block188Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part000
    + surrogateDiagTailX0RatChunk000Sub000Block188Part001
    + surrogateDiagTailX0RatChunk000Sub000Block188Part002
    + surrogateDiagTailX0RatChunk000Sub000Block188Part003
    + surrogateDiagTailX0RatChunk000Sub000Block188Part004
    + surrogateDiagTailX0RatChunk000Sub000Block188Part005
    + surrogateDiagTailX0RatChunk000Sub000Block188Part006
    + surrogateDiagTailX0RatChunk000Sub000Block188Part007
    + surrogateDiagTailX0RatChunk000Sub000Block188Part008
    + surrogateDiagTailX0RatChunk000Sub000Block188Part009

def surrogateDiagonalTailChunk000Sub000Block188MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block188Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block188Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part010
    + surrogateDiagTailX0RatChunk000Sub000Block188Part011
    + surrogateDiagTailX0RatChunk000Sub000Block188Part012
    + surrogateDiagTailX0RatChunk000Sub000Block188Part013
    + surrogateDiagTailX0RatChunk000Sub000Block188Part014
    + surrogateDiagTailX0RatChunk000Sub000Block188Part015
    + surrogateDiagTailX0RatChunk000Sub000Block188Part016
    + surrogateDiagTailX0RatChunk000Sub000Block188Part017
    + surrogateDiagTailX0RatChunk000Sub000Block188Part018
    + surrogateDiagTailX0RatChunk000Sub000Block188Part019

def surrogateDiagonalTailChunk000Sub000Block188TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block188Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block188Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block188Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part020
    + surrogateDiagTailX0RatChunk000Sub000Block188Part021
    + surrogateDiagTailX0RatChunk000Sub000Block188Part022
    + surrogateDiagTailX0RatChunk000Sub000Block188Part023
    + surrogateDiagTailX0RatChunk000Sub000Block188Part024

def surrogateDiagonalTailChunk000Sub000Block188Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block188HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block188MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block188TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block188 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block188Part000
    + surrogateDiagTailX0RatChunk000Sub000Block188Part001
    + surrogateDiagTailX0RatChunk000Sub000Block188Part002
    + surrogateDiagTailX0RatChunk000Sub000Block188Part003
    + surrogateDiagTailX0RatChunk000Sub000Block188Part004
    + surrogateDiagTailX0RatChunk000Sub000Block188Part005
    + surrogateDiagTailX0RatChunk000Sub000Block188Part006
    + surrogateDiagTailX0RatChunk000Sub000Block188Part007
    + surrogateDiagTailX0RatChunk000Sub000Block188Part008
    + surrogateDiagTailX0RatChunk000Sub000Block188Part009
    + surrogateDiagTailX0RatChunk000Sub000Block188Part010
    + surrogateDiagTailX0RatChunk000Sub000Block188Part011
    + surrogateDiagTailX0RatChunk000Sub000Block188Part012
    + surrogateDiagTailX0RatChunk000Sub000Block188Part013
    + surrogateDiagTailX0RatChunk000Sub000Block188Part014
    + surrogateDiagTailX0RatChunk000Sub000Block188Part015
    + surrogateDiagTailX0RatChunk000Sub000Block188Part016
    + surrogateDiagTailX0RatChunk000Sub000Block188Part017
    + surrogateDiagTailX0RatChunk000Sub000Block188Part018
    + surrogateDiagTailX0RatChunk000Sub000Block188Part019
    + surrogateDiagTailX0RatChunk000Sub000Block188Part020
    + surrogateDiagTailX0RatChunk000Sub000Block188Part021
    + surrogateDiagTailX0RatChunk000Sub000Block188Part022
    + surrogateDiagTailX0RatChunk000Sub000Block188Part023
    + surrogateDiagTailX0RatChunk000Sub000Block188Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block188_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block188Head + surrogateDiagTailX0RatChunk000Sub000Block188Mid + surrogateDiagTailX0RatChunk000Sub000Block188Tail =
      surrogateDiagTailX0RatChunk000Sub000Block188 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block188Head surrogateDiagTailX0RatChunk000Sub000Block188Mid surrogateDiagTailX0RatChunk000Sub000Block188Tail surrogateDiagTailX0RatChunk000Sub000Block188
  ring

def SurrogateDiagonalTailChunk000Sub000Block188HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block188HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block188Head

def SurrogateDiagonalTailChunk000Sub000Block188MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block188MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block188Mid

def SurrogateDiagonalTailChunk000Sub000Block188TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block188TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block188Tail

theorem surrogateDiagonalTailChunk000Sub000Block188_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block188HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block188MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block188TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block188Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block188 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block188HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block188MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block188TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block188Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block188_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
