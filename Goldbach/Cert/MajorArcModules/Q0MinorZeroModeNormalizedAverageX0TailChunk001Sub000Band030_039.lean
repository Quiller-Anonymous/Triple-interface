import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [30,40). -/

/-- Block 030 covers tail-support indices [10750,10775) and q from 17729 to 17770. -/

def TailChunk001Sub000Block030Part000SupportExplicit : Finset ℕ :=
  ([17729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block030Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17729
    = surrogateDiagTailX0RatChunk001Sub000Block030Part000

theorem surrogateDiagonalTailChunk001Sub000Block030Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part000] using hcert

def TailChunk001Sub000Block030Part001SupportExplicit : Finset ℕ :=
  ([17731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part001 : ℚ :=
  (15845574325 : ℚ) / 1592130560675807232

def SurrogateDiagonalTailChunk001Sub000Block030Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17731
    = surrogateDiagTailX0RatChunk001Sub000Block030Part001

theorem surrogateDiagonalTailChunk001Sub000Block030Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part001] using hcert

def TailChunk001Sub000Block030Part002SupportExplicit : Finset ℕ :=
  ([17733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part002 : ℚ :=
  (357269362875 : ℚ) / 6708820555090362368

def SurrogateDiagonalTailChunk001Sub000Block030Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17733
    = surrogateDiagTailX0RatChunk001Sub000Block030Part002

theorem surrogateDiagonalTailChunk001Sub000Block030Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part002] using hcert

def TailChunk001Sub000Block030Part003SupportExplicit : Finset ℕ :=
  ([17734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block030Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17734
    = surrogateDiagTailX0RatChunk001Sub000Block030Part003

theorem surrogateDiagonalTailChunk001Sub000Block030Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part003] using hcert

def TailChunk001Sub000Block030Part004SupportExplicit : Finset ℕ :=
  ([17735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part004 : ℚ :=
  (524233402675 : ℚ) / 33736536503486355456

def SurrogateDiagonalTailChunk001Sub000Block030Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17735
    = surrogateDiagTailX0RatChunk001Sub000Block030Part004

theorem surrogateDiagonalTailChunk001Sub000Block030Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part004] using hcert

def TailChunk001Sub000Block030Part005SupportExplicit : Finset ℕ :=
  ([17737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block030Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17737
    = surrogateDiagTailX0RatChunk001Sub000Block030Part005

theorem surrogateDiagonalTailChunk001Sub000Block030Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part005] using hcert

def TailChunk001Sub000Block030Part006SupportExplicit : Finset ℕ :=
  ([17741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part006 : ℚ :=
  (41975228075 : ℚ) / 116511112017859313664

def SurrogateDiagonalTailChunk001Sub000Block030Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17741
    = surrogateDiagTailX0RatChunk001Sub000Block030Part006

theorem surrogateDiagonalTailChunk001Sub000Block030Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part006] using hcert

def TailChunk001Sub000Block030Part007SupportExplicit : Finset ℕ :=
  ([17742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part007 : ℚ :=
  (8542908025 : ℚ) / 47729247403252512

def SurrogateDiagonalTailChunk001Sub000Block030Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17742
    = surrogateDiagTailX0RatChunk001Sub000Block030Part007

theorem surrogateDiagonalTailChunk001Sub000Block030Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part007] using hcert

def TailChunk001Sub000Block030Part008SupportExplicit : Finset ℕ :=
  ([17743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part008 : ℚ :=
  (8698309047 : ℚ) / 2251260468706662400

def SurrogateDiagonalTailChunk001Sub000Block030Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17743
    = surrogateDiagTailX0RatChunk001Sub000Block030Part008

theorem surrogateDiagonalTailChunk001Sub000Block030Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part008] using hcert

def TailChunk001Sub000Block030Part009SupportExplicit : Finset ℕ :=
  ([17746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part009 : ℚ :=
  (51539191525 : ℚ) / 4126095648952246656

def SurrogateDiagonalTailChunk001Sub000Block030Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17746
    = surrogateDiagTailX0RatChunk001Sub000Block030Part009

theorem surrogateDiagonalTailChunk001Sub000Block030Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part009] using hcert

def TailChunk001Sub000Block030Part010SupportExplicit : Finset ℕ :=
  ([17747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block030Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17747
    = surrogateDiagTailX0RatChunk001Sub000Block030Part010

theorem surrogateDiagonalTailChunk001Sub000Block030Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part010] using hcert

def TailChunk001Sub000Block030Part011SupportExplicit : Finset ℕ :=
  ([17749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block030Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17749
    = surrogateDiagTailX0RatChunk001Sub000Block030Part011

theorem surrogateDiagonalTailChunk001Sub000Block030Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part011] using hcert

def TailChunk001Sub000Block030Part012SupportExplicit : Finset ℕ :=
  ([17751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part012 : ℚ :=
  (10847149343 : ℚ) / 220194658477670400

def SurrogateDiagonalTailChunk001Sub000Block030Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17751
    = surrogateDiagTailX0RatChunk001Sub000Block030Part012

theorem surrogateDiagonalTailChunk001Sub000Block030Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part012] using hcert

def TailChunk001Sub000Block030Part013SupportExplicit : Finset ℕ :=
  ([17753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part013 : ℚ :=
  (6086602873 : ℚ) / 8917883668345651200

def SurrogateDiagonalTailChunk001Sub000Block030Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17753
    = surrogateDiagTailX0RatChunk001Sub000Block030Part013

theorem surrogateDiagonalTailChunk001Sub000Block030Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part013] using hcert

def TailChunk001Sub000Block030Part014SupportExplicit : Finset ℕ :=
  ([17754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part014 : ℚ :=
  (21219480749 : ℚ) / 41277749707161600

def SurrogateDiagonalTailChunk001Sub000Block030Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17754
    = surrogateDiagTailX0RatChunk001Sub000Block030Part014

theorem surrogateDiagonalTailChunk001Sub000Block030Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part014] using hcert

def TailChunk001Sub000Block030Part015SupportExplicit : Finset ℕ :=
  ([17755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part015 : ℚ :=
  (59934928325 : ℚ) / 3289214353304715264

def SurrogateDiagonalTailChunk001Sub000Block030Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17755
    = surrogateDiagTailX0RatChunk001Sub000Block030Part015

theorem surrogateDiagonalTailChunk001Sub000Block030Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part015] using hcert

def TailChunk001Sub000Block030Part016SupportExplicit : Finset ℕ :=
  ([17758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part016 : ℚ :=
  (3136364525 : ℚ) / 169959484886197248

def SurrogateDiagonalTailChunk001Sub000Block030Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17758
    = surrogateDiagTailX0RatChunk001Sub000Block030Part016

theorem surrogateDiagonalTailChunk001Sub000Block030Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part016] using hcert

def TailChunk001Sub000Block030Part017SupportExplicit : Finset ℕ :=
  ([17759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part017 : ℚ :=
  (307877858275 : ℚ) / 38038181079186118656

def SurrogateDiagonalTailChunk001Sub000Block030Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17759
    = surrogateDiagTailX0RatChunk001Sub000Block030Part017

theorem surrogateDiagonalTailChunk001Sub000Block030Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part017] using hcert

def TailChunk001Sub000Block030Part018SupportExplicit : Finset ℕ :=
  ([17761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block030Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17761
    = surrogateDiagTailX0RatChunk001Sub000Block030Part018

theorem surrogateDiagonalTailChunk001Sub000Block030Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part018] using hcert

def TailChunk001Sub000Block030Part019SupportExplicit : Finset ℕ :=
  ([17762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part019 : ℚ :=
  (58224829525 : ℚ) / 14272686594391813248

def SurrogateDiagonalTailChunk001Sub000Block030Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17762
    = surrogateDiagTailX0RatChunk001Sub000Block030Part019

theorem surrogateDiagonalTailChunk001Sub000Block030Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part019] using hcert

def TailChunk001Sub000Block030Part020SupportExplicit : Finset ℕ :=
  ([17763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part020 : ℚ :=
  (86665032589 : ℚ) / 1689297952032000000

def SurrogateDiagonalTailChunk001Sub000Block030Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17763
    = surrogateDiagTailX0RatChunk001Sub000Block030Part020

theorem surrogateDiagonalTailChunk001Sub000Block030Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part020] using hcert

def TailChunk001Sub000Block030Part021SupportExplicit : Finset ℕ :=
  ([17765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part021 : ℚ :=
  (35354710061 : ℚ) / 880778633910681600

def SurrogateDiagonalTailChunk001Sub000Block030Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17765
    = surrogateDiagTailX0RatChunk001Sub000Block030Part021

theorem surrogateDiagonalTailChunk001Sub000Block030Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part021] using hcert

def TailChunk001Sub000Block030Part022SupportExplicit : Finset ℕ :=
  ([17767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part022 : ℚ :=
  (42192816725 : ℚ) / 117152603204874200064

def SurrogateDiagonalTailChunk001Sub000Block030Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17767
    = surrogateDiagTailX0RatChunk001Sub000Block030Part022

theorem surrogateDiagonalTailChunk001Sub000Block030Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part022] using hcert

def TailChunk001Sub000Block030Part023SupportExplicit : Finset ℕ :=
  ([17769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part023 : ℚ :=
  (156607520675 : ℚ) / 3514733639786884032

def SurrogateDiagonalTailChunk001Sub000Block030Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17769
    = surrogateDiagTailX0RatChunk001Sub000Block030Part023

theorem surrogateDiagonalTailChunk001Sub000Block030Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part023] using hcert

def TailChunk001Sub000Block030Part024SupportExplicit : Finset ℕ :=
  ([17770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block030Part024 : ℚ :=
  (296210783225 : ℚ) / 3184261121351614464

def SurrogateDiagonalTailChunk001Sub000Block030Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17770
    = surrogateDiagTailX0RatChunk001Sub000Block030Part024

theorem surrogateDiagonalTailChunk001Sub000Block030Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block030Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block030Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block030Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block030Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block030Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block030HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block030Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block030Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block030Part000
    + surrogateDiagTailX0RatChunk001Sub000Block030Part001
    + surrogateDiagTailX0RatChunk001Sub000Block030Part002
    + surrogateDiagTailX0RatChunk001Sub000Block030Part003
    + surrogateDiagTailX0RatChunk001Sub000Block030Part004
    + surrogateDiagTailX0RatChunk001Sub000Block030Part005
    + surrogateDiagTailX0RatChunk001Sub000Block030Part006
    + surrogateDiagTailX0RatChunk001Sub000Block030Part007
    + surrogateDiagTailX0RatChunk001Sub000Block030Part008
    + surrogateDiagTailX0RatChunk001Sub000Block030Part009

def surrogateDiagonalTailChunk001Sub000Block030MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block030Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block030Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block030Part010
    + surrogateDiagTailX0RatChunk001Sub000Block030Part011
    + surrogateDiagTailX0RatChunk001Sub000Block030Part012
    + surrogateDiagTailX0RatChunk001Sub000Block030Part013
    + surrogateDiagTailX0RatChunk001Sub000Block030Part014
    + surrogateDiagTailX0RatChunk001Sub000Block030Part015
    + surrogateDiagTailX0RatChunk001Sub000Block030Part016
    + surrogateDiagTailX0RatChunk001Sub000Block030Part017
    + surrogateDiagTailX0RatChunk001Sub000Block030Part018
    + surrogateDiagTailX0RatChunk001Sub000Block030Part019

def surrogateDiagonalTailChunk001Sub000Block030TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block030Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block030Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block030Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block030Part020
    + surrogateDiagTailX0RatChunk001Sub000Block030Part021
    + surrogateDiagTailX0RatChunk001Sub000Block030Part022
    + surrogateDiagTailX0RatChunk001Sub000Block030Part023
    + surrogateDiagTailX0RatChunk001Sub000Block030Part024

def surrogateDiagonalTailChunk001Sub000Block030Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block030HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block030MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block030TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block030 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block030Part000
    + surrogateDiagTailX0RatChunk001Sub000Block030Part001
    + surrogateDiagTailX0RatChunk001Sub000Block030Part002
    + surrogateDiagTailX0RatChunk001Sub000Block030Part003
    + surrogateDiagTailX0RatChunk001Sub000Block030Part004
    + surrogateDiagTailX0RatChunk001Sub000Block030Part005
    + surrogateDiagTailX0RatChunk001Sub000Block030Part006
    + surrogateDiagTailX0RatChunk001Sub000Block030Part007
    + surrogateDiagTailX0RatChunk001Sub000Block030Part008
    + surrogateDiagTailX0RatChunk001Sub000Block030Part009
    + surrogateDiagTailX0RatChunk001Sub000Block030Part010
    + surrogateDiagTailX0RatChunk001Sub000Block030Part011
    + surrogateDiagTailX0RatChunk001Sub000Block030Part012
    + surrogateDiagTailX0RatChunk001Sub000Block030Part013
    + surrogateDiagTailX0RatChunk001Sub000Block030Part014
    + surrogateDiagTailX0RatChunk001Sub000Block030Part015
    + surrogateDiagTailX0RatChunk001Sub000Block030Part016
    + surrogateDiagTailX0RatChunk001Sub000Block030Part017
    + surrogateDiagTailX0RatChunk001Sub000Block030Part018
    + surrogateDiagTailX0RatChunk001Sub000Block030Part019
    + surrogateDiagTailX0RatChunk001Sub000Block030Part020
    + surrogateDiagTailX0RatChunk001Sub000Block030Part021
    + surrogateDiagTailX0RatChunk001Sub000Block030Part022
    + surrogateDiagTailX0RatChunk001Sub000Block030Part023
    + surrogateDiagTailX0RatChunk001Sub000Block030Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block030_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block030Head + surrogateDiagTailX0RatChunk001Sub000Block030Mid + surrogateDiagTailX0RatChunk001Sub000Block030Tail =
      surrogateDiagTailX0RatChunk001Sub000Block030 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block030Head surrogateDiagTailX0RatChunk001Sub000Block030Mid surrogateDiagTailX0RatChunk001Sub000Block030Tail surrogateDiagTailX0RatChunk001Sub000Block030
  ring

def SurrogateDiagonalTailChunk001Sub000Block030HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block030HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block030Head

def SurrogateDiagonalTailChunk001Sub000Block030MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block030MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block030Mid

def SurrogateDiagonalTailChunk001Sub000Block030TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block030TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block030Tail

theorem surrogateDiagonalTailChunk001Sub000Block030_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block030HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block030MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block030TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block030Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block030 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block030HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block030MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block030TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block030Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block030_eq_head_add_mid_add_tail

/-- Block 031 covers tail-support indices [10775,10800) and q from 17771 to 17810. -/

def TailChunk001Sub000Block031Part000SupportExplicit : Finset ℕ :=
  ([17771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part000 : ℚ :=
  (78327002275 : ℚ) / 30088697635826961408

def SurrogateDiagonalTailChunk001Sub000Block031Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17771
    = surrogateDiagTailX0RatChunk001Sub000Block031Part000

theorem surrogateDiagonalTailChunk001Sub000Block031Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part000] using hcert

def TailChunk001Sub000Block031Part001SupportExplicit : Finset ℕ :=
  ([17773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part001 : ℚ :=
  (403447139075 : ℚ) / 67230808777381184064

def SurrogateDiagonalTailChunk001Sub000Block031Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17773
    = surrogateDiagTailX0RatChunk001Sub000Block031Part001

theorem surrogateDiagonalTailChunk001Sub000Block031Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part001] using hcert

def TailChunk001Sub000Block031Part002SupportExplicit : Finset ℕ :=
  ([17774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block031Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17774
    = surrogateDiagTailX0RatChunk001Sub000Block031Part002

theorem surrogateDiagonalTailChunk001Sub000Block031Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part002] using hcert

def TailChunk001Sub000Block031Part003SupportExplicit : Finset ℕ :=
  ([17777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part003 : ℚ :=
  (5757102625 : ℚ) / 6341408870603046912

def SurrogateDiagonalTailChunk001Sub000Block031Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17777
    = surrogateDiagTailX0RatChunk001Sub000Block031Part003

theorem surrogateDiagonalTailChunk001Sub000Block031Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part003] using hcert

def TailChunk001Sub000Block031Part004SupportExplicit : Finset ℕ :=
  ([17778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part004 : ℚ :=
  (548542996325 : ℚ) / 1539774285701204544

def SurrogateDiagonalTailChunk001Sub000Block031Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17778
    = surrogateDiagTailX0RatChunk001Sub000Block031Part004

theorem surrogateDiagonalTailChunk001Sub000Block031Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part004] using hcert

def TailChunk001Sub000Block031Part005SupportExplicit : Finset ℕ :=
  ([17779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part005 : ℚ :=
  (133647349325 : ℚ) / 104029566284828304384

def SurrogateDiagonalTailChunk001Sub000Block031Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17779
    = surrogateDiagTailX0RatChunk001Sub000Block031Part005

theorem surrogateDiagonalTailChunk001Sub000Block031Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part005] using hcert

def TailChunk001Sub000Block031Part006SupportExplicit : Finset ℕ :=
  ([17781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part006 : ℚ :=
  (1097733644675 : ℚ) / 24669675360693962304

def SurrogateDiagonalTailChunk001Sub000Block031Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17781
    = surrogateDiagTailX0RatChunk001Sub000Block031Part006

theorem surrogateDiagonalTailChunk001Sub000Block031Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part006] using hcert

def TailChunk001Sub000Block031Part007SupportExplicit : Finset ℕ :=
  ([17782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part007 : ℚ :=
  (5852775325 : ℚ) / 450635122230165504

def SurrogateDiagonalTailChunk001Sub000Block031Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17782
    = surrogateDiagTailX0RatChunk001Sub000Block031Part007

theorem surrogateDiagonalTailChunk001Sub000Block031Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part007] using hcert

def TailChunk001Sub000Block031Part008SupportExplicit : Finset ℕ :=
  ([17783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block031Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17783
    = surrogateDiagTailX0RatChunk001Sub000Block031Part008

theorem surrogateDiagonalTailChunk001Sub000Block031Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part008] using hcert

def TailChunk001Sub000Block031Part009SupportExplicit : Finset ℕ :=
  ([17785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part009 : ℚ :=
  (263857247625 : ℚ) / 34118708128296042496

def SurrogateDiagonalTailChunk001Sub000Block031Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17785
    = surrogateDiagTailX0RatChunk001Sub000Block031Part009

theorem surrogateDiagonalTailChunk001Sub000Block031Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part009] using hcert

def TailChunk001Sub000Block031Part010SupportExplicit : Finset ℕ :=
  ([17786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block031Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17786
    = surrogateDiagTailX0RatChunk001Sub000Block031Part010

theorem surrogateDiagonalTailChunk001Sub000Block031Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part010] using hcert

def TailChunk001Sub000Block031Part011SupportExplicit : Finset ℕ :=
  ([17789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block031Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17789
    = surrogateDiagTailX0RatChunk001Sub000Block031Part011

theorem surrogateDiagonalTailChunk001Sub000Block031Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part011] using hcert

def TailChunk001Sub000Block031Part012SupportExplicit : Finset ℕ :=
  ([17790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part012 : ℚ :=
  (322062165075 : ℚ) / 419326567420788736

def SurrogateDiagonalTailChunk001Sub000Block031Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17790
    = surrogateDiagTailX0RatChunk001Sub000Block031Part012

theorem surrogateDiagonalTailChunk001Sub000Block031Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part012] using hcert

def TailChunk001Sub000Block031Part013SupportExplicit : Finset ℕ :=
  ([17791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block031Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17791
    = surrogateDiagTailX0RatChunk001Sub000Block031Part013

theorem surrogateDiagonalTailChunk001Sub000Block031Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part013] using hcert

def TailChunk001Sub000Block031Part014SupportExplicit : Finset ℕ :=
  ([17794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part014 : ℚ :=
  (2434857101 : ℚ) / 33599038464000000

def SurrogateDiagonalTailChunk001Sub000Block031Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17794
    = surrogateDiagTailX0RatChunk001Sub000Block031Part014

theorem surrogateDiagonalTailChunk001Sub000Block031Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part014] using hcert

def TailChunk001Sub000Block031Part015SupportExplicit : Finset ℕ :=
  ([17795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part015 : ℚ :=
  (792460992625 : ℚ) / 102586591221678655488

def SurrogateDiagonalTailChunk001Sub000Block031Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17795
    = surrogateDiagTailX0RatChunk001Sub000Block031Part015

theorem surrogateDiagonalTailChunk001Sub000Block031Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part015] using hcert

def TailChunk001Sub000Block031Part016SupportExplicit : Finset ℕ :=
  ([17798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part016 : ℚ :=
  (990824353 : ℚ) / 42631664877649920

def SurrogateDiagonalTailChunk001Sub000Block031Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17798
    = surrogateDiagTailX0RatChunk001Sub000Block031Part016

theorem surrogateDiagonalTailChunk001Sub000Block031Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part016] using hcert

def TailChunk001Sub000Block031Part017SupportExplicit : Finset ℕ :=
  ([17799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part017 : ℚ :=
  (719837748625 : ℚ) / 12818065698991374336

def SurrogateDiagonalTailChunk001Sub000Block031Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17799
    = surrogateDiagTailX0RatChunk001Sub000Block031Part017

theorem surrogateDiagonalTailChunk001Sub000Block031Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part017] using hcert

def TailChunk001Sub000Block031Part018SupportExplicit : Finset ℕ :=
  ([17801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part018 : ℚ :=
  (404716885175 : ℚ) / 67655646690200829504

def SurrogateDiagonalTailChunk001Sub000Block031Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17801
    = surrogateDiagTailX0RatChunk001Sub000Block031Part018

theorem surrogateDiagonalTailChunk001Sub000Block031Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part018] using hcert

def TailChunk001Sub000Block031Part019SupportExplicit : Finset ℕ :=
  ([17803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part019 : ℚ :=
  (34897943225 : ℚ) / 25184323378395058176

def SurrogateDiagonalTailChunk001Sub000Block031Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17803
    = surrogateDiagTailX0RatChunk001Sub000Block031Part019

theorem surrogateDiagonalTailChunk001Sub000Block031Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part019] using hcert

def TailChunk001Sub000Block031Part020SupportExplicit : Finset ℕ :=
  ([17805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part020 : ℚ :=
  (121042184725 : ℚ) / 1266501126193563648

def SurrogateDiagonalTailChunk001Sub000Block031Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17805
    = surrogateDiagTailX0RatChunk001Sub000Block031Part020

theorem surrogateDiagonalTailChunk001Sub000Block031Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part020] using hcert

def TailChunk001Sub000Block031Part021SupportExplicit : Finset ℕ :=
  ([17806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part021 : ℚ :=
  (2430601975 : ℚ) / 320845091667416064

def SurrogateDiagonalTailChunk001Sub000Block031Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17806
    = surrogateDiagTailX0RatChunk001Sub000Block031Part021

theorem surrogateDiagonalTailChunk001Sub000Block031Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part021] using hcert

def TailChunk001Sub000Block031Part022SupportExplicit : Finset ℕ :=
  ([17807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block031Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17807
    = surrogateDiagTailX0RatChunk001Sub000Block031Part022

theorem surrogateDiagonalTailChunk001Sub000Block031Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part022] using hcert

def TailChunk001Sub000Block031Part023SupportExplicit : Finset ℕ :=
  ([17809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part023 : ℚ :=
  (19751674747 : ℚ) / 6854896774989955200

def SurrogateDiagonalTailChunk001Sub000Block031Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17809
    = surrogateDiagTailX0RatChunk001Sub000Block031Part023

theorem surrogateDiagonalTailChunk001Sub000Block031Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part023] using hcert

def TailChunk001Sub000Block031Part024SupportExplicit : Finset ℕ :=
  ([17810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block031Part024 : ℚ :=
  (692119322575 : ℚ) / 4540957548324323328

def SurrogateDiagonalTailChunk001Sub000Block031Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17810
    = surrogateDiagTailX0RatChunk001Sub000Block031Part024

theorem surrogateDiagonalTailChunk001Sub000Block031Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block031Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block031Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block031Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block031Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block031Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block031HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block031Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block031Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block031Part000
    + surrogateDiagTailX0RatChunk001Sub000Block031Part001
    + surrogateDiagTailX0RatChunk001Sub000Block031Part002
    + surrogateDiagTailX0RatChunk001Sub000Block031Part003
    + surrogateDiagTailX0RatChunk001Sub000Block031Part004
    + surrogateDiagTailX0RatChunk001Sub000Block031Part005
    + surrogateDiagTailX0RatChunk001Sub000Block031Part006
    + surrogateDiagTailX0RatChunk001Sub000Block031Part007
    + surrogateDiagTailX0RatChunk001Sub000Block031Part008
    + surrogateDiagTailX0RatChunk001Sub000Block031Part009

def surrogateDiagonalTailChunk001Sub000Block031MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block031Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block031Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block031Part010
    + surrogateDiagTailX0RatChunk001Sub000Block031Part011
    + surrogateDiagTailX0RatChunk001Sub000Block031Part012
    + surrogateDiagTailX0RatChunk001Sub000Block031Part013
    + surrogateDiagTailX0RatChunk001Sub000Block031Part014
    + surrogateDiagTailX0RatChunk001Sub000Block031Part015
    + surrogateDiagTailX0RatChunk001Sub000Block031Part016
    + surrogateDiagTailX0RatChunk001Sub000Block031Part017
    + surrogateDiagTailX0RatChunk001Sub000Block031Part018
    + surrogateDiagTailX0RatChunk001Sub000Block031Part019

def surrogateDiagonalTailChunk001Sub000Block031TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block031Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block031Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block031Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block031Part020
    + surrogateDiagTailX0RatChunk001Sub000Block031Part021
    + surrogateDiagTailX0RatChunk001Sub000Block031Part022
    + surrogateDiagTailX0RatChunk001Sub000Block031Part023
    + surrogateDiagTailX0RatChunk001Sub000Block031Part024

def surrogateDiagonalTailChunk001Sub000Block031Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block031HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block031MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block031TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block031 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block031Part000
    + surrogateDiagTailX0RatChunk001Sub000Block031Part001
    + surrogateDiagTailX0RatChunk001Sub000Block031Part002
    + surrogateDiagTailX0RatChunk001Sub000Block031Part003
    + surrogateDiagTailX0RatChunk001Sub000Block031Part004
    + surrogateDiagTailX0RatChunk001Sub000Block031Part005
    + surrogateDiagTailX0RatChunk001Sub000Block031Part006
    + surrogateDiagTailX0RatChunk001Sub000Block031Part007
    + surrogateDiagTailX0RatChunk001Sub000Block031Part008
    + surrogateDiagTailX0RatChunk001Sub000Block031Part009
    + surrogateDiagTailX0RatChunk001Sub000Block031Part010
    + surrogateDiagTailX0RatChunk001Sub000Block031Part011
    + surrogateDiagTailX0RatChunk001Sub000Block031Part012
    + surrogateDiagTailX0RatChunk001Sub000Block031Part013
    + surrogateDiagTailX0RatChunk001Sub000Block031Part014
    + surrogateDiagTailX0RatChunk001Sub000Block031Part015
    + surrogateDiagTailX0RatChunk001Sub000Block031Part016
    + surrogateDiagTailX0RatChunk001Sub000Block031Part017
    + surrogateDiagTailX0RatChunk001Sub000Block031Part018
    + surrogateDiagTailX0RatChunk001Sub000Block031Part019
    + surrogateDiagTailX0RatChunk001Sub000Block031Part020
    + surrogateDiagTailX0RatChunk001Sub000Block031Part021
    + surrogateDiagTailX0RatChunk001Sub000Block031Part022
    + surrogateDiagTailX0RatChunk001Sub000Block031Part023
    + surrogateDiagTailX0RatChunk001Sub000Block031Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block031_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block031Head + surrogateDiagTailX0RatChunk001Sub000Block031Mid + surrogateDiagTailX0RatChunk001Sub000Block031Tail =
      surrogateDiagTailX0RatChunk001Sub000Block031 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block031Head surrogateDiagTailX0RatChunk001Sub000Block031Mid surrogateDiagTailX0RatChunk001Sub000Block031Tail surrogateDiagTailX0RatChunk001Sub000Block031
  ring

def SurrogateDiagonalTailChunk001Sub000Block031HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block031HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block031Head

def SurrogateDiagonalTailChunk001Sub000Block031MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block031MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block031Mid

def SurrogateDiagonalTailChunk001Sub000Block031TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block031TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block031Tail

theorem surrogateDiagonalTailChunk001Sub000Block031_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block031HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block031MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block031TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block031Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block031 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block031HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block031MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block031TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block031Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block031_eq_head_add_mid_add_tail

/-- Block 032 covers tail-support indices [10800,10825) and q from 17813 to 17851. -/

def TailChunk001Sub000Block032Part000SupportExplicit : Finset ℕ :=
  ([17813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part000 : ℚ :=
  (885318725 : ℚ) / 1554920001958748544

def SurrogateDiagonalTailChunk001Sub000Block032Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17813
    = surrogateDiagTailX0RatChunk001Sub000Block032Part000

theorem surrogateDiagonalTailChunk001Sub000Block032Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part000] using hcert

def TailChunk001Sub000Block032Part001SupportExplicit : Finset ℕ :=
  ([17814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part001 : ℚ :=
  (550766301275 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk001Sub000Block032Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17814
    = surrogateDiagTailX0RatChunk001Sub000Block032Part001

theorem surrogateDiagonalTailChunk001Sub000Block032Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part001] using hcert

def TailChunk001Sub000Block032Part002SupportExplicit : Finset ℕ :=
  ([17815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part002 : ℚ :=
  (1217259855625 : ℚ) / 55249286631743029248

def SurrogateDiagonalTailChunk001Sub000Block032Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17815
    = surrogateDiagTailX0RatChunk001Sub000Block032Part002

theorem surrogateDiagonalTailChunk001Sub000Block032Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part002] using hcert

def TailChunk001Sub000Block032Part003SupportExplicit : Finset ℕ :=
  ([17817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part003 : ℚ :=
  (1102182644525 : ℚ) / 24870105004482337344

def SurrogateDiagonalTailChunk001Sub000Block032Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17817
    = surrogateDiagTailX0RatChunk001Sub000Block032Part003

theorem surrogateDiagonalTailChunk001Sub000Block032Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part003] using hcert

def TailChunk001Sub000Block032Part004SupportExplicit : Finset ℕ :=
  ([17818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part004 : ℚ :=
  (2571339157 : ℚ) / 573012189522000000

def SurrogateDiagonalTailChunk001Sub000Block032Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17818
    = surrogateDiagTailX0RatChunk001Sub000Block032Part004

theorem surrogateDiagonalTailChunk001Sub000Block032Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part004] using hcert

def TailChunk001Sub000Block032Part005SupportExplicit : Finset ℕ :=
  ([17819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part005 : ℚ :=
  (42425129075 : ℚ) / 118443528802251777024

def SurrogateDiagonalTailChunk001Sub000Block032Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17819
    = surrogateDiagTailX0RatChunk001Sub000Block032Part005

theorem surrogateDiagonalTailChunk001Sub000Block032Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part005] using hcert

def TailChunk001Sub000Block032Part006SupportExplicit : Finset ℕ :=
  ([17821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part006 : ℚ :=
  (478509173 : ℚ) / 1172597753906250000

def SurrogateDiagonalTailChunk001Sub000Block032Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17821
    = surrogateDiagTailX0RatChunk001Sub000Block032Part006

theorem surrogateDiagonalTailChunk001Sub000Block032Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part006] using hcert

def TailChunk001Sub000Block032Part007SupportExplicit : Finset ℕ :=
  ([17822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part007 : ℚ :=
  (1034087575 : ℚ) / 13336819127419392

def SurrogateDiagonalTailChunk001Sub000Block032Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17822
    = surrogateDiagTailX0RatChunk001Sub000Block032Part007

theorem surrogateDiagonalTailChunk001Sub000Block032Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part007] using hcert

def TailChunk001Sub000Block032Part008SupportExplicit : Finset ℕ :=
  ([17823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part008 : ℚ :=
  (2164747049425 : ℚ) / 35869985109335605248

def SurrogateDiagonalTailChunk001Sub000Block032Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17823
    = surrogateDiagTailX0RatChunk001Sub000Block032Part008

theorem surrogateDiagonalTailChunk001Sub000Block032Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part008] using hcert

def TailChunk001Sub000Block032Part009SupportExplicit : Finset ℕ :=
  ([17826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part009 : ℚ :=
  (2207725453 : ℚ) / 12451814154457920

def SurrogateDiagonalTailChunk001Sub000Block032Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17826
    = surrogateDiagTailX0RatChunk001Sub000Block032Part009

theorem surrogateDiagonalTailChunk001Sub000Block032Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part009] using hcert

def TailChunk001Sub000Block032Part010SupportExplicit : Finset ℕ :=
  ([17827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block032Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17827
    = surrogateDiagTailX0RatChunk001Sub000Block032Part010

theorem surrogateDiagonalTailChunk001Sub000Block032Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part010] using hcert

def TailChunk001Sub000Block032Part011SupportExplicit : Finset ℕ :=
  ([17830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part011 : ℚ :=
  (74552839025 : ℚ) / 806877557208873216

def SurrogateDiagonalTailChunk001Sub000Block032Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17830
    = surrogateDiagTailX0RatChunk001Sub000Block032Part011

theorem surrogateDiagonalTailChunk001Sub000Block032Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part011] using hcert

def TailChunk001Sub000Block032Part012SupportExplicit : Finset ℕ :=
  ([17831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part012 : ℚ :=
  (19800225277 : ℚ) / 6888852855072000000

def SurrogateDiagonalTailChunk001Sub000Block032Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17831
    = surrogateDiagTailX0RatChunk001Sub000Block032Part012

theorem surrogateDiagonalTailChunk001Sub000Block032Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part012] using hcert

def TailChunk001Sub000Block032Part013SupportExplicit : Finset ℕ :=
  ([17833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part013 : ℚ :=
  (347944036525 : ℚ) / 197675078574290239488

def SurrogateDiagonalTailChunk001Sub000Block032Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17833
    = surrogateDiagTailX0RatChunk001Sub000Block032Part013

theorem surrogateDiagonalTailChunk001Sub000Block032Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part013] using hcert

def TailChunk001Sub000Block032Part014SupportExplicit : Finset ℕ :=
  ([17834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part014 : ℚ :=
  (38460341 : ℚ) / 6192974769684480

def SurrogateDiagonalTailChunk001Sub000Block032Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17834
    = surrogateDiagTailX0RatChunk001Sub000Block032Part014

theorem surrogateDiagonalTailChunk001Sub000Block032Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part014] using hcert

def TailChunk001Sub000Block032Part015SupportExplicit : Finset ℕ :=
  ([17835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part015 : ℚ :=
  (28499570737 : ℚ) / 644642432561971200

def SurrogateDiagonalTailChunk001Sub000Block032Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17835
    = surrogateDiagTailX0RatChunk001Sub000Block032Part015

theorem surrogateDiagonalTailChunk001Sub000Block032Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part015] using hcert

def TailChunk001Sub000Block032Part016SupportExplicit : Finset ℕ :=
  ([17837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block032Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17837
    = surrogateDiagTailX0RatChunk001Sub000Block032Part016

theorem surrogateDiagonalTailChunk001Sub000Block032Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part016] using hcert

def TailChunk001Sub000Block032Part017SupportExplicit : Finset ℕ :=
  ([17839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block032Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17839
    = surrogateDiagTailX0RatChunk001Sub000Block032Part017

theorem surrogateDiagonalTailChunk001Sub000Block032Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part017] using hcert

def TailChunk001Sub000Block032Part018SupportExplicit : Finset ℕ :=
  ([17841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part018 : ℚ :=
  (11105827375 : ℚ) / 2210969404961980416

def SurrogateDiagonalTailChunk001Sub000Block032Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17841
    = surrogateDiagTailX0RatChunk001Sub000Block032Part018

theorem surrogateDiagonalTailChunk001Sub000Block032Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part018] using hcert

def TailChunk001Sub000Block032Part019SupportExplicit : Finset ℕ :=
  ([17842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part019 : ℚ :=
  (995673487 : ℚ) / 43055330344200000

def SurrogateDiagonalTailChunk001Sub000Block032Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17842
    = surrogateDiagTailX0RatChunk001Sub000Block032Part019

theorem surrogateDiagonalTailChunk001Sub000Block032Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part019] using hcert

def TailChunk001Sub000Block032Part020SupportExplicit : Finset ℕ :=
  ([17843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part020 : ℚ :=
  (406625253575 : ℚ) / 68296674793671926784

def SurrogateDiagonalTailChunk001Sub000Block032Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17843
    = surrogateDiagTailX0RatChunk001Sub000Block032Part020

theorem surrogateDiagonalTailChunk001Sub000Block032Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part020] using hcert

def TailChunk001Sub000Block032Part021SupportExplicit : Finset ℕ :=
  ([17845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part021 : ℚ :=
  (893820653125 : ℚ) / 90057398092760383488

def SurrogateDiagonalTailChunk001Sub000Block032Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17845
    = surrogateDiagTailX0RatChunk001Sub000Block032Part021

theorem surrogateDiagonalTailChunk001Sub000Block032Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part021] using hcert

def TailChunk001Sub000Block032Part022SupportExplicit : Finset ℕ :=
  ([17846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block032Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17846
    = surrogateDiagTailX0RatChunk001Sub000Block032Part022

theorem surrogateDiagonalTailChunk001Sub000Block032Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part022] using hcert

def TailChunk001Sub000Block032Part023SupportExplicit : Finset ℕ :=
  ([17849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part023 : ℚ :=
  (25468511675 : ℚ) / 13123215267941302272

def SurrogateDiagonalTailChunk001Sub000Block032Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17849
    = surrogateDiagTailX0RatChunk001Sub000Block032Part023

theorem surrogateDiagonalTailChunk001Sub000Block032Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part023] using hcert

def TailChunk001Sub000Block032Part024SupportExplicit : Finset ℕ :=
  ([17851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block032Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block032Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17851
    = surrogateDiagTailX0RatChunk001Sub000Block032Part024

theorem surrogateDiagonalTailChunk001Sub000Block032Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block032Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block032Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block032Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block032Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block032Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block032HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block032Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block032Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block032Part000
    + surrogateDiagTailX0RatChunk001Sub000Block032Part001
    + surrogateDiagTailX0RatChunk001Sub000Block032Part002
    + surrogateDiagTailX0RatChunk001Sub000Block032Part003
    + surrogateDiagTailX0RatChunk001Sub000Block032Part004
    + surrogateDiagTailX0RatChunk001Sub000Block032Part005
    + surrogateDiagTailX0RatChunk001Sub000Block032Part006
    + surrogateDiagTailX0RatChunk001Sub000Block032Part007
    + surrogateDiagTailX0RatChunk001Sub000Block032Part008
    + surrogateDiagTailX0RatChunk001Sub000Block032Part009

def surrogateDiagonalTailChunk001Sub000Block032MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block032Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block032Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block032Part010
    + surrogateDiagTailX0RatChunk001Sub000Block032Part011
    + surrogateDiagTailX0RatChunk001Sub000Block032Part012
    + surrogateDiagTailX0RatChunk001Sub000Block032Part013
    + surrogateDiagTailX0RatChunk001Sub000Block032Part014
    + surrogateDiagTailX0RatChunk001Sub000Block032Part015
    + surrogateDiagTailX0RatChunk001Sub000Block032Part016
    + surrogateDiagTailX0RatChunk001Sub000Block032Part017
    + surrogateDiagTailX0RatChunk001Sub000Block032Part018
    + surrogateDiagTailX0RatChunk001Sub000Block032Part019

def surrogateDiagonalTailChunk001Sub000Block032TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block032Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block032Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block032Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block032Part020
    + surrogateDiagTailX0RatChunk001Sub000Block032Part021
    + surrogateDiagTailX0RatChunk001Sub000Block032Part022
    + surrogateDiagTailX0RatChunk001Sub000Block032Part023
    + surrogateDiagTailX0RatChunk001Sub000Block032Part024

def surrogateDiagonalTailChunk001Sub000Block032Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block032HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block032MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block032TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block032 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block032Part000
    + surrogateDiagTailX0RatChunk001Sub000Block032Part001
    + surrogateDiagTailX0RatChunk001Sub000Block032Part002
    + surrogateDiagTailX0RatChunk001Sub000Block032Part003
    + surrogateDiagTailX0RatChunk001Sub000Block032Part004
    + surrogateDiagTailX0RatChunk001Sub000Block032Part005
    + surrogateDiagTailX0RatChunk001Sub000Block032Part006
    + surrogateDiagTailX0RatChunk001Sub000Block032Part007
    + surrogateDiagTailX0RatChunk001Sub000Block032Part008
    + surrogateDiagTailX0RatChunk001Sub000Block032Part009
    + surrogateDiagTailX0RatChunk001Sub000Block032Part010
    + surrogateDiagTailX0RatChunk001Sub000Block032Part011
    + surrogateDiagTailX0RatChunk001Sub000Block032Part012
    + surrogateDiagTailX0RatChunk001Sub000Block032Part013
    + surrogateDiagTailX0RatChunk001Sub000Block032Part014
    + surrogateDiagTailX0RatChunk001Sub000Block032Part015
    + surrogateDiagTailX0RatChunk001Sub000Block032Part016
    + surrogateDiagTailX0RatChunk001Sub000Block032Part017
    + surrogateDiagTailX0RatChunk001Sub000Block032Part018
    + surrogateDiagTailX0RatChunk001Sub000Block032Part019
    + surrogateDiagTailX0RatChunk001Sub000Block032Part020
    + surrogateDiagTailX0RatChunk001Sub000Block032Part021
    + surrogateDiagTailX0RatChunk001Sub000Block032Part022
    + surrogateDiagTailX0RatChunk001Sub000Block032Part023
    + surrogateDiagTailX0RatChunk001Sub000Block032Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block032_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block032Head + surrogateDiagTailX0RatChunk001Sub000Block032Mid + surrogateDiagTailX0RatChunk001Sub000Block032Tail =
      surrogateDiagTailX0RatChunk001Sub000Block032 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block032Head surrogateDiagTailX0RatChunk001Sub000Block032Mid surrogateDiagTailX0RatChunk001Sub000Block032Tail surrogateDiagTailX0RatChunk001Sub000Block032
  ring

def SurrogateDiagonalTailChunk001Sub000Block032HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block032HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block032Head

def SurrogateDiagonalTailChunk001Sub000Block032MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block032MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block032Mid

def SurrogateDiagonalTailChunk001Sub000Block032TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block032TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block032Tail

theorem surrogateDiagonalTailChunk001Sub000Block032_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block032HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block032MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block032TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block032Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block032 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block032HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block032MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block032TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block032Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block032_eq_head_add_mid_add_tail

/-- Block 033 covers tail-support indices [10825,10850) and q from 17853 to 17891. -/

def TailChunk001Sub000Block033Part000SupportExplicit : Finset ℕ :=
  ([17853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part000 : ℚ :=
  (6687553463 : ℚ) / 680380528896000000

def SurrogateDiagonalTailChunk001Sub000Block033Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17853
    = surrogateDiagTailX0RatChunk001Sub000Block033Part000

theorem surrogateDiagonalTailChunk001Sub000Block033Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part000] using hcert

def TailChunk001Sub000Block033Part001SupportExplicit : Finset ℕ :=
  ([17854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part001 : ℚ :=
  (26116975 : ℚ) / 6421467814035456

def SurrogateDiagonalTailChunk001Sub000Block033Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17854
    = surrogateDiagTailX0RatChunk001Sub000Block033Part001

theorem surrogateDiagonalTailChunk001Sub000Block033Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part001] using hcert

def TailChunk001Sub000Block033Part002SupportExplicit : Finset ℕ :=
  ([17855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part002 : ℚ :=
  (6382455929 : ℚ) / 831820608026634240

def SurrogateDiagonalTailChunk001Sub000Block033Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17855
    = surrogateDiagTailX0RatChunk001Sub000Block033Part002

theorem surrogateDiagonalTailChunk001Sub000Block033Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part002] using hcert

def TailChunk001Sub000Block033Part003SupportExplicit : Finset ℕ :=
  ([17857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part003 : ℚ :=
  (16331245093 : ℚ) / 5480908772562000000

def SurrogateDiagonalTailChunk001Sub000Block033Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17857
    = surrogateDiagTailX0RatChunk001Sub000Block033Part003

theorem surrogateDiagonalTailChunk001Sub000Block033Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part003] using hcert

def TailChunk001Sub000Block033Part004SupportExplicit : Finset ℕ :=
  ([17858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part004 : ℚ :=
  (1245735015625 : ℚ) / 3971765452967903232

def SurrogateDiagonalTailChunk001Sub000Block033Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17858
    = surrogateDiagTailX0RatChunk001Sub000Block033Part004

theorem surrogateDiagonalTailChunk001Sub000Block033Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part004] using hcert

def TailChunk001Sub000Block033Part005SupportExplicit : Finset ℕ :=
  ([17859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part005 : ℚ :=
  (8857200404725 : ℚ) / 50210960788137443328

def SurrogateDiagonalTailChunk001Sub000Block033Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17859
    = surrogateDiagTailX0RatChunk001Sub000Block033Part005

theorem surrogateDiagonalTailChunk001Sub000Block033Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part005] using hcert

def TailChunk001Sub000Block033Part006SupportExplicit : Finset ℕ :=
  ([17861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part006 : ℚ :=
  (9598099790075 : ℚ) / 116511112017859313664

def SurrogateDiagonalTailChunk001Sub000Block033Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17861
    = surrogateDiagTailX0RatChunk001Sub000Block033Part006

theorem surrogateDiagonalTailChunk001Sub000Block033Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part006] using hcert

def TailChunk001Sub000Block033Part007SupportExplicit : Finset ℕ :=
  ([17862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part007 : ℚ :=
  (68898759725 : ℚ) / 62274279703707648

def SurrogateDiagonalTailChunk001Sub000Block033Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17862
    = surrogateDiagTailX0RatChunk001Sub000Block033Part007

theorem surrogateDiagonalTailChunk001Sub000Block033Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part007] using hcert

def TailChunk001Sub000Block033Part008SupportExplicit : Finset ℕ :=
  ([17863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part008 : ℚ :=
  (4985730765625 : ℚ) / 63633704619515896242

def SurrogateDiagonalTailChunk001Sub000Block033Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17863
    = surrogateDiagTailX0RatChunk001Sub000Block033Part008

theorem surrogateDiagonalTailChunk001Sub000Block033Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part008] using hcert

def TailChunk001Sub000Block033Part009SupportExplicit : Finset ℕ :=
  ([17866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part009 : ℚ :=
  (1246851390625 : ℚ) / 3978888097139088672

def SurrogateDiagonalTailChunk001Sub000Block033Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17866
    = surrogateDiagTailX0RatChunk001Sub000Block033Part009

theorem surrogateDiagonalTailChunk001Sub000Block033Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part009] using hcert

def TailChunk001Sub000Block033Part010SupportExplicit : Finset ℕ :=
  ([17867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part010 : ℚ :=
  (238962691081 : ℚ) / 2655844982784000000

def SurrogateDiagonalTailChunk001Sub000Block033Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17867
    = surrogateDiagTailX0RatChunk001Sub000Block033Part010

theorem surrogateDiagonalTailChunk001Sub000Block033Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part010] using hcert

def TailChunk001Sub000Block033Part011SupportExplicit : Finset ℕ :=
  ([17869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part011 : ℚ :=
  (19433809932025 : ℚ) / 239708079320594867328

def SurrogateDiagonalTailChunk001Sub000Block033Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17869
    = surrogateDiagTailX0RatChunk001Sub000Block033Part011

theorem surrogateDiagonalTailChunk001Sub000Block033Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part011] using hcert

def TailChunk001Sub000Block033Part012SupportExplicit : Finset ℕ :=
  ([17870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part012 : ℚ :=
  (1196776339275 : ℚ) / 2171057809348335616

def SurrogateDiagonalTailChunk001Sub000Block033Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17870
    = surrogateDiagTailX0RatChunk001Sub000Block033Part012

theorem surrogateDiagonalTailChunk001Sub000Block033Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part012] using hcert

def TailChunk001Sub000Block033Part013SupportExplicit : Finset ℕ :=
  ([17871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part013 : ℚ :=
  (1537345140625 : ℚ) / 5100263077665964032

def SurrogateDiagonalTailChunk001Sub000Block033Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17871
    = surrogateDiagTailX0RatChunk001Sub000Block033Part013

theorem surrogateDiagonalTailChunk001Sub000Block033Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part013] using hcert

def TailChunk001Sub000Block033Part014SupportExplicit : Finset ℕ :=
  ([17873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part014 : ℚ :=
  (257199678041 : ℚ) / 3141246392325734400

def SurrogateDiagonalTailChunk001Sub000Block033Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17873
    = surrogateDiagTailX0RatChunk001Sub000Block033Part014

theorem surrogateDiagonalTailChunk001Sub000Block033Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part014] using hcert

def TailChunk001Sub000Block033Part015SupportExplicit : Finset ℕ :=
  ([17877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part015 : ℚ :=
  (170091616721 : ℚ) / 905500743936000000

def SurrogateDiagonalTailChunk001Sub000Block033Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17877
    = surrogateDiagTailX0RatChunk001Sub000Block033Part015

theorem surrogateDiagonalTailChunk001Sub000Block033Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part015] using hcert

def TailChunk001Sub000Block033Part016SupportExplicit : Finset ℕ :=
  ([17878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part016 : ℚ :=
  (220620075875 : ℚ) / 477267710110811136

def SurrogateDiagonalTailChunk001Sub000Block033Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17878
    = surrogateDiagTailX0RatChunk001Sub000Block033Part016

theorem surrogateDiagonalTailChunk001Sub000Block033Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part016] using hcert

def TailChunk001Sub000Block033Part017SupportExplicit : Finset ℕ :=
  ([17879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part017 : ℚ :=
  (724834180369 : ℚ) / 8197629480552499200

def SurrogateDiagonalTailChunk001Sub000Block033Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17879
    = surrogateDiagTailX0RatChunk001Sub000Block033Part017

theorem surrogateDiagonalTailChunk001Sub000Block033Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part017] using hcert

def TailChunk001Sub000Block033Part018SupportExplicit : Finset ℕ :=
  ([17881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part018 : ℚ :=
  (7993254025 : ℚ) / 102224950293238272

def SurrogateDiagonalTailChunk001Sub000Block033Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17881
    = surrogateDiagTailX0RatChunk001Sub000Block033Part018

theorem surrogateDiagonalTailChunk001Sub000Block033Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part018] using hcert

def TailChunk001Sub000Block033Part019SupportExplicit : Finset ℕ :=
  ([17882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part019 : ℚ :=
  (1998537025 : ℚ) / 6389059393327392

def SurrogateDiagonalTailChunk001Sub000Block033Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17882
    = surrogateDiagTailX0RatChunk001Sub000Block033Part019

theorem surrogateDiagonalTailChunk001Sub000Block033Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part019] using hcert

def TailChunk001Sub000Block033Part020SupportExplicit : Finset ℕ :=
  ([17886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part020 : ℚ :=
  (1078209937 : ℚ) / 944972956800000

def SurrogateDiagonalTailChunk001Sub000Block033Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17886
    = surrogateDiagTailX0RatChunk001Sub000Block033Part020

theorem surrogateDiagonalTailChunk001Sub000Block033Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part020] using hcert

def TailChunk001Sub000Block033Part021SupportExplicit : Finset ℕ :=
  ([17887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part021 : ℚ :=
  (47098350307 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub000Block033Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17887
    = surrogateDiagTailX0RatChunk001Sub000Block033Part021

theorem surrogateDiagonalTailChunk001Sub000Block033Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part021] using hcert

def TailChunk001Sub000Block033Part022SupportExplicit : Finset ℕ :=
  ([17889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part022 : ℚ :=
  (8526740869225 : ℚ) / 45525347794608979968

def SurrogateDiagonalTailChunk001Sub000Block033Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17889
    = surrogateDiagTailX0RatChunk001Sub000Block033Part022

theorem surrogateDiagonalTailChunk001Sub000Block033Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part022] using hcert

def TailChunk001Sub000Block033Part023SupportExplicit : Finset ℕ :=
  ([17890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part023 : ℚ :=
  (3598371768925 : ℚ) / 6542396818767249408

def SurrogateDiagonalTailChunk001Sub000Block033Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17890
    = surrogateDiagTailX0RatChunk001Sub000Block033Part023

theorem surrogateDiagonalTailChunk001Sub000Block033Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part023] using hcert

def TailChunk001Sub000Block033Part024SupportExplicit : Finset ℕ :=
  ([17891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block033Part024 : ℚ :=
  (8002197025 : ℚ) / 102453833383752882

def SurrogateDiagonalTailChunk001Sub000Block033Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17891
    = surrogateDiagTailX0RatChunk001Sub000Block033Part024

theorem surrogateDiagonalTailChunk001Sub000Block033Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block033Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block033Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block033Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block033Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block033Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block033HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block033Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block033Part000
    + surrogateDiagTailX0RatChunk001Sub000Block033Part001
    + surrogateDiagTailX0RatChunk001Sub000Block033Part002
    + surrogateDiagTailX0RatChunk001Sub000Block033Part003
    + surrogateDiagTailX0RatChunk001Sub000Block033Part004
    + surrogateDiagTailX0RatChunk001Sub000Block033Part005
    + surrogateDiagTailX0RatChunk001Sub000Block033Part006
    + surrogateDiagTailX0RatChunk001Sub000Block033Part007
    + surrogateDiagTailX0RatChunk001Sub000Block033Part008
    + surrogateDiagTailX0RatChunk001Sub000Block033Part009

def surrogateDiagonalTailChunk001Sub000Block033MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block033Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block033Part010
    + surrogateDiagTailX0RatChunk001Sub000Block033Part011
    + surrogateDiagTailX0RatChunk001Sub000Block033Part012
    + surrogateDiagTailX0RatChunk001Sub000Block033Part013
    + surrogateDiagTailX0RatChunk001Sub000Block033Part014
    + surrogateDiagTailX0RatChunk001Sub000Block033Part015
    + surrogateDiagTailX0RatChunk001Sub000Block033Part016
    + surrogateDiagTailX0RatChunk001Sub000Block033Part017
    + surrogateDiagTailX0RatChunk001Sub000Block033Part018
    + surrogateDiagTailX0RatChunk001Sub000Block033Part019

def surrogateDiagonalTailChunk001Sub000Block033TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block033Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block033Part020
    + surrogateDiagTailX0RatChunk001Sub000Block033Part021
    + surrogateDiagTailX0RatChunk001Sub000Block033Part022
    + surrogateDiagTailX0RatChunk001Sub000Block033Part023
    + surrogateDiagTailX0RatChunk001Sub000Block033Part024

def surrogateDiagonalTailChunk001Sub000Block033Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block033HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block033MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block033TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block033 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block033Part000
    + surrogateDiagTailX0RatChunk001Sub000Block033Part001
    + surrogateDiagTailX0RatChunk001Sub000Block033Part002
    + surrogateDiagTailX0RatChunk001Sub000Block033Part003
    + surrogateDiagTailX0RatChunk001Sub000Block033Part004
    + surrogateDiagTailX0RatChunk001Sub000Block033Part005
    + surrogateDiagTailX0RatChunk001Sub000Block033Part006
    + surrogateDiagTailX0RatChunk001Sub000Block033Part007
    + surrogateDiagTailX0RatChunk001Sub000Block033Part008
    + surrogateDiagTailX0RatChunk001Sub000Block033Part009
    + surrogateDiagTailX0RatChunk001Sub000Block033Part010
    + surrogateDiagTailX0RatChunk001Sub000Block033Part011
    + surrogateDiagTailX0RatChunk001Sub000Block033Part012
    + surrogateDiagTailX0RatChunk001Sub000Block033Part013
    + surrogateDiagTailX0RatChunk001Sub000Block033Part014
    + surrogateDiagTailX0RatChunk001Sub000Block033Part015
    + surrogateDiagTailX0RatChunk001Sub000Block033Part016
    + surrogateDiagTailX0RatChunk001Sub000Block033Part017
    + surrogateDiagTailX0RatChunk001Sub000Block033Part018
    + surrogateDiagTailX0RatChunk001Sub000Block033Part019
    + surrogateDiagTailX0RatChunk001Sub000Block033Part020
    + surrogateDiagTailX0RatChunk001Sub000Block033Part021
    + surrogateDiagTailX0RatChunk001Sub000Block033Part022
    + surrogateDiagTailX0RatChunk001Sub000Block033Part023
    + surrogateDiagTailX0RatChunk001Sub000Block033Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block033_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block033Head + surrogateDiagTailX0RatChunk001Sub000Block033Mid + surrogateDiagTailX0RatChunk001Sub000Block033Tail =
      surrogateDiagTailX0RatChunk001Sub000Block033 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block033Head surrogateDiagTailX0RatChunk001Sub000Block033Mid surrogateDiagTailX0RatChunk001Sub000Block033Tail surrogateDiagTailX0RatChunk001Sub000Block033
  ring

def SurrogateDiagonalTailChunk001Sub000Block033HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block033HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block033Head

def SurrogateDiagonalTailChunk001Sub000Block033MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block033MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block033Mid

def SurrogateDiagonalTailChunk001Sub000Block033TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block033TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block033Tail

theorem surrogateDiagonalTailChunk001Sub000Block033_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block033HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block033MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block033TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block033Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block033 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block033HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block033MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block033TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block033Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block033_eq_head_add_mid_add_tail

/-- Block 034 covers tail-support indices [10850,10875) and q from 17893 to 17933. -/

def TailChunk001Sub000Block034Part000SupportExplicit : Finset ℕ :=
  ([17893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part000 : ℚ :=
  (18769687221025 : ℚ) / 221300213497956139008

def SurrogateDiagonalTailChunk001Sub000Block034Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17893
    = surrogateDiagTailX0RatChunk001Sub000Block034Part000

theorem surrogateDiagonalTailChunk001Sub000Block034Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part000] using hcert

def TailChunk001Sub000Block034Part001SupportExplicit : Finset ℕ :=
  ([17894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part001 : ℚ :=
  (779073477375 : ℚ) / 2212550714985171968

def SurrogateDiagonalTailChunk001Sub000Block034Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17894
    = surrogateDiagTailX0RatChunk001Sub000Block034Part001

theorem surrogateDiagonalTailChunk001Sub000Block034Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part001] using hcert

def TailChunk001Sub000Block034Part002SupportExplicit : Finset ℕ :=
  ([17895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part002 : ℚ :=
  (1554719629675 : ℚ) / 5169301190137085952

def SurrogateDiagonalTailChunk001Sub000Block034Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17895
    = surrogateDiagTailX0RatChunk001Sub000Block034Part002

theorem surrogateDiagonalTailChunk001Sub000Block034Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part002] using hcert

def TailChunk001Sub000Block034Part003SupportExplicit : Finset ℕ :=
  ([17897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part003 : ℚ :=
  (42147715411 : ℚ) / 436967394964792200

def SurrogateDiagonalTailChunk001Sub000Block034Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17897
    = surrogateDiagTailX0RatChunk001Sub000Block034Part003

theorem surrogateDiagonalTailChunk001Sub000Block034Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part003] using hcert

def TailChunk001Sub000Block034Part004SupportExplicit : Finset ℕ :=
  ([17898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part004 : ℚ :=
  (2566853734675 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk001Sub000Block034Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17898
    = surrogateDiagTailX0RatChunk001Sub000Block034Part004

theorem surrogateDiagonalTailChunk001Sub000Block034Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part004] using hcert

def TailChunk001Sub000Block034Part005SupportExplicit : Finset ℕ :=
  ([17899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part005 : ℚ :=
  (15110726913025 : ℚ) / 138316903671331473408

def SurrogateDiagonalTailChunk001Sub000Block034Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17899
    = surrogateDiagTailX0RatChunk001Sub000Block034Part005

theorem surrogateDiagonalTailChunk001Sub000Block034Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part005] using hcert

def TailChunk001Sub000Block034Part006SupportExplicit : Finset ℕ :=
  ([17902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part006 : ℚ :=
  (80120401 : ℚ) / 256707751534050

def SurrogateDiagonalTailChunk001Sub000Block034Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17902
    = surrogateDiagTailX0RatChunk001Sub000Block034Part006

theorem surrogateDiagonalTailChunk001Sub000Block034Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part006] using hcert

def TailChunk001Sub000Block034Part007SupportExplicit : Finset ℕ :=
  ([17903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part007 : ℚ :=
  (5008084515625 : ℚ) / 64205625121320811602

def SurrogateDiagonalTailChunk001Sub000Block034Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17903
    = surrogateDiagTailX0RatChunk001Sub000Block034Part007

theorem surrogateDiagonalTailChunk001Sub000Block034Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part007] using hcert

def TailChunk001Sub000Block034Part008SupportExplicit : Finset ℕ :=
  ([17905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part008 : ℚ :=
  (544798283839 : ℚ) / 4205899801133875200

def SurrogateDiagonalTailChunk001Sub000Block034Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17905
    = surrogateDiagTailX0RatChunk001Sub000Block034Part008

theorem surrogateDiagonalTailChunk001Sub000Block034Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part008] using hcert

def TailChunk001Sub000Block034Part009SupportExplicit : Finset ℕ :=
  ([17906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part009 : ℚ :=
  (221311890575 : ℚ) / 480267026636567616

def SurrogateDiagonalTailChunk001Sub000Block034Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17906
    = surrogateDiagTailX0RatChunk001Sub000Block034Part009

theorem surrogateDiagonalTailChunk001Sub000Block034Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part009] using hcert

def TailChunk001Sub000Block034Part010SupportExplicit : Finset ℕ :=
  ([17907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part010 : ℚ :=
  (409901525 : ℚ) / 2177385690900168

def SurrogateDiagonalTailChunk001Sub000Block034Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17907
    = surrogateDiagTailX0RatChunk001Sub000Block034Part010

theorem surrogateDiagonalTailChunk001Sub000Block034Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part010] using hcert

def TailChunk001Sub000Block034Part011SupportExplicit : Finset ℕ :=
  ([17909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part011 : ℚ :=
  (5011441890625 : ℚ) / 64291744541567322912

def SurrogateDiagonalTailChunk001Sub000Block034Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17909
    = surrogateDiagTailX0RatChunk001Sub000Block034Part011

theorem surrogateDiagonalTailChunk001Sub000Block034Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part011] using hcert

def TailChunk001Sub000Block034Part012SupportExplicit : Finset ℕ :=
  ([17911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part012 : ℚ :=
  (8020098025 : ℚ) / 102912752412405522

def SurrogateDiagonalTailChunk001Sub000Block034Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17911
    = surrogateDiagTailX0RatChunk001Sub000Block034Part012

theorem surrogateDiagonalTailChunk001Sub000Block034Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part012] using hcert

def TailChunk001Sub000Block034Part013SupportExplicit : Finset ℕ :=
  ([17913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part013 : ℚ :=
  (6899424698425 : ℚ) / 27321857515324735488

def SurrogateDiagonalTailChunk001Sub000Block034Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17913
    = surrogateDiagTailX0RatChunk001Sub000Block034Part013

theorem surrogateDiagonalTailChunk001Sub000Block034Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part013] using hcert

def TailChunk001Sub000Block034Part014SupportExplicit : Finset ℕ :=
  ([17915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part014 : ℚ :=
  (267332796875 : ℚ) / 2195472051464651136

def SurrogateDiagonalTailChunk001Sub000Block034Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17915
    = surrogateDiagTailX0RatChunk001Sub000Block034Part014

theorem surrogateDiagonalTailChunk001Sub000Block034Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part014] using hcert

def TailChunk001Sub000Block034Part015SupportExplicit : Finset ℕ :=
  ([17917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part015 : ℚ :=
  (323824523873 : ℚ) / 3148310541769113600

def SurrogateDiagonalTailChunk001Sub000Block034Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17917
    = surrogateDiagTailX0RatChunk001Sub000Block034Part015

theorem surrogateDiagonalTailChunk001Sub000Block034Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part015] using hcert

def TailChunk001Sub000Block034Part016SupportExplicit : Finset ℕ :=
  ([17921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part016 : ℚ :=
  (8029056025 : ℚ) / 103142789209915392

def SurrogateDiagonalTailChunk001Sub000Block034Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17921
    = surrogateDiagTailX0RatChunk001Sub000Block034Part016

theorem surrogateDiagonalTailChunk001Sub000Block034Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part016] using hcert

def TailChunk001Sub000Block034Part017SupportExplicit : Finset ℕ :=
  ([17922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part017 : ℚ :=
  (1312862054675 : ℚ) / 1330912972842614784

def SurrogateDiagonalTailChunk001Sub000Block034Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17922
    = surrogateDiagTailX0RatChunk001Sub000Block034Part017

theorem surrogateDiagonalTailChunk001Sub000Block034Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part017] using hcert

def TailChunk001Sub000Block034Part018SupportExplicit : Finset ℕ :=
  ([17923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part018 : ℚ :=
  (5019280140625 : ℚ) / 64493026754440068882

def SurrogateDiagonalTailChunk001Sub000Block034Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17923
    = surrogateDiagTailX0RatChunk001Sub000Block034Part018

theorem surrogateDiagonalTailChunk001Sub000Block034Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part018] using hcert

def TailChunk001Sub000Block034Part019SupportExplicit : Finset ℕ :=
  ([17926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part019 : ℚ :=
  (1255240140625 : ℚ) / 4032613743159546642

def SurrogateDiagonalTailChunk001Sub000Block034Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17926
    = surrogateDiagTailX0RatChunk001Sub000Block034Part019

theorem surrogateDiagonalTailChunk001Sub000Block034Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part019] using hcert

def TailChunk001Sub000Block034Part020SupportExplicit : Finset ℕ :=
  ([17927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part020 : ℚ :=
  (1640349451625 : ℚ) / 12396273314323562496

def SurrogateDiagonalTailChunk001Sub000Block034Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17927
    = surrogateDiagTailX0RatChunk001Sub000Block034Part020

theorem surrogateDiagonalTailChunk001Sub000Block034Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part020] using hcert

def TailChunk001Sub000Block034Part021SupportExplicit : Finset ℕ :=
  ([17929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part021 : ℚ :=
  (5022641265625 : ℚ) / 64579435084992287232

def SurrogateDiagonalTailChunk001Sub000Block034Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17929
    = surrogateDiagTailX0RatChunk001Sub000Block034Part021

theorem surrogateDiagonalTailChunk001Sub000Block034Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part021] using hcert

def TailChunk001Sub000Block034Part022SupportExplicit : Finset ℕ :=
  ([17930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part022 : ℚ :=
  (10447465859 : ℚ) / 14696219424153600

def SurrogateDiagonalTailChunk001Sub000Block034Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17930
    = surrogateDiagTailX0RatChunk001Sub000Block034Part022

theorem surrogateDiagonalTailChunk001Sub000Block034Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part022] using hcert

def TailChunk001Sub000Block034Part023SupportExplicit : Finset ℕ :=
  ([17931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part023 : ℚ :=
  (2126304896125 : ℚ) / 11287567421626470912

def SurrogateDiagonalTailChunk001Sub000Block034Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17931
    = surrogateDiagTailX0RatChunk001Sub000Block034Part023

theorem surrogateDiagonalTailChunk001Sub000Block034Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part023] using hcert

def TailChunk001Sub000Block034Part024SupportExplicit : Finset ℕ :=
  ([17933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block034Part024 : ℚ :=
  (90344310575 : ℚ) / 1117854488797561008

def SurrogateDiagonalTailChunk001Sub000Block034Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17933
    = surrogateDiagTailX0RatChunk001Sub000Block034Part024

theorem surrogateDiagonalTailChunk001Sub000Block034Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block034Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block034Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block034Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block034Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block034Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block034HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block034Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block034Part000
    + surrogateDiagTailX0RatChunk001Sub000Block034Part001
    + surrogateDiagTailX0RatChunk001Sub000Block034Part002
    + surrogateDiagTailX0RatChunk001Sub000Block034Part003
    + surrogateDiagTailX0RatChunk001Sub000Block034Part004
    + surrogateDiagTailX0RatChunk001Sub000Block034Part005
    + surrogateDiagTailX0RatChunk001Sub000Block034Part006
    + surrogateDiagTailX0RatChunk001Sub000Block034Part007
    + surrogateDiagTailX0RatChunk001Sub000Block034Part008
    + surrogateDiagTailX0RatChunk001Sub000Block034Part009

def surrogateDiagonalTailChunk001Sub000Block034MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block034Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block034Part010
    + surrogateDiagTailX0RatChunk001Sub000Block034Part011
    + surrogateDiagTailX0RatChunk001Sub000Block034Part012
    + surrogateDiagTailX0RatChunk001Sub000Block034Part013
    + surrogateDiagTailX0RatChunk001Sub000Block034Part014
    + surrogateDiagTailX0RatChunk001Sub000Block034Part015
    + surrogateDiagTailX0RatChunk001Sub000Block034Part016
    + surrogateDiagTailX0RatChunk001Sub000Block034Part017
    + surrogateDiagTailX0RatChunk001Sub000Block034Part018
    + surrogateDiagTailX0RatChunk001Sub000Block034Part019

def surrogateDiagonalTailChunk001Sub000Block034TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block034Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block034Part020
    + surrogateDiagTailX0RatChunk001Sub000Block034Part021
    + surrogateDiagTailX0RatChunk001Sub000Block034Part022
    + surrogateDiagTailX0RatChunk001Sub000Block034Part023
    + surrogateDiagTailX0RatChunk001Sub000Block034Part024

def surrogateDiagonalTailChunk001Sub000Block034Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block034HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block034MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block034TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block034 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block034Part000
    + surrogateDiagTailX0RatChunk001Sub000Block034Part001
    + surrogateDiagTailX0RatChunk001Sub000Block034Part002
    + surrogateDiagTailX0RatChunk001Sub000Block034Part003
    + surrogateDiagTailX0RatChunk001Sub000Block034Part004
    + surrogateDiagTailX0RatChunk001Sub000Block034Part005
    + surrogateDiagTailX0RatChunk001Sub000Block034Part006
    + surrogateDiagTailX0RatChunk001Sub000Block034Part007
    + surrogateDiagTailX0RatChunk001Sub000Block034Part008
    + surrogateDiagTailX0RatChunk001Sub000Block034Part009
    + surrogateDiagTailX0RatChunk001Sub000Block034Part010
    + surrogateDiagTailX0RatChunk001Sub000Block034Part011
    + surrogateDiagTailX0RatChunk001Sub000Block034Part012
    + surrogateDiagTailX0RatChunk001Sub000Block034Part013
    + surrogateDiagTailX0RatChunk001Sub000Block034Part014
    + surrogateDiagTailX0RatChunk001Sub000Block034Part015
    + surrogateDiagTailX0RatChunk001Sub000Block034Part016
    + surrogateDiagTailX0RatChunk001Sub000Block034Part017
    + surrogateDiagTailX0RatChunk001Sub000Block034Part018
    + surrogateDiagTailX0RatChunk001Sub000Block034Part019
    + surrogateDiagTailX0RatChunk001Sub000Block034Part020
    + surrogateDiagTailX0RatChunk001Sub000Block034Part021
    + surrogateDiagTailX0RatChunk001Sub000Block034Part022
    + surrogateDiagTailX0RatChunk001Sub000Block034Part023
    + surrogateDiagTailX0RatChunk001Sub000Block034Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block034_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block034Head + surrogateDiagTailX0RatChunk001Sub000Block034Mid + surrogateDiagTailX0RatChunk001Sub000Block034Tail =
      surrogateDiagTailX0RatChunk001Sub000Block034 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block034Head surrogateDiagTailX0RatChunk001Sub000Block034Mid surrogateDiagTailX0RatChunk001Sub000Block034Tail surrogateDiagTailX0RatChunk001Sub000Block034
  ring

def SurrogateDiagonalTailChunk001Sub000Block034HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block034HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block034Head

def SurrogateDiagonalTailChunk001Sub000Block034MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block034MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block034Mid

def SurrogateDiagonalTailChunk001Sub000Block034TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block034TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block034Tail

theorem surrogateDiagonalTailChunk001Sub000Block034_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block034HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block034MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block034TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block034Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block034 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block034HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block034MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block034TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block034Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block034_eq_head_add_mid_add_tail

/-- Block 035 covers tail-support indices [10875,10900) and q from 17935 to 17974. -/

def TailChunk001Sub000Block035Part000SupportExplicit : Finset ℕ :=
  ([17935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part000 : ℚ :=
  (5697759463 : ℚ) / 40290152035123200

def SurrogateDiagonalTailChunk001Sub000Block035Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17935
    = surrogateDiagTailX0RatChunk001Sub000Block035Part000

theorem surrogateDiagonalTailChunk001Sub000Block035Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part000] using hcert

def TailChunk001Sub000Block035Part001SupportExplicit : Finset ℕ :=
  ([17938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part001 : ℚ :=
  (1256921265625 : ℚ) / 4043423826436035072

def SurrogateDiagonalTailChunk001Sub000Block035Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17938
    = surrogateDiagTailX0RatChunk001Sub000Block035Part001

theorem surrogateDiagonalTailChunk001Sub000Block035Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part001] using hcert

def TailChunk001Sub000Block035Part002SupportExplicit : Finset ℕ :=
  ([17939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part002 : ℚ :=
  (5028245640625 : ℚ) / 64723641884424105042

def SurrogateDiagonalTailChunk001Sub000Block035Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17939
    = surrogateDiagTailX0RatChunk001Sub000Block035Part002

theorem surrogateDiagonalTailChunk001Sub000Block035Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part002] using hcert

def TailChunk001Sub000Block035Part003SupportExplicit : Finset ℕ :=
  ([17941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part003 : ℚ :=
  (510740636203 : ℚ) / 3755292685251379200

def SurrogateDiagonalTailChunk001Sub000Block035Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17941
    = surrogateDiagTailX0RatChunk001Sub000Block035Part003

theorem surrogateDiagonalTailChunk001Sub000Block035Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part003] using hcert

def TailChunk001Sub000Block035Part004SupportExplicit : Finset ℕ :=
  ([17942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part004 : ℚ :=
  (2011971025 : ℚ) / 6475251220095762

def SurrogateDiagonalTailChunk001Sub000Block035Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17942
    = surrogateDiagTailX0RatChunk001Sub000Block035Part004

theorem surrogateDiagonalTailChunk001Sub000Block035Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part004] using hcert

def TailChunk001Sub000Block035Part005SupportExplicit : Finset ℕ :=
  ([17943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part005 : ℚ :=
  (357628976077 : ℚ) / 2046499151042611200

def SurrogateDiagonalTailChunk001Sub000Block035Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17943
    = surrogateDiagTailX0RatChunk001Sub000Block035Part005

theorem surrogateDiagonalTailChunk001Sub000Block035Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part005] using hcert

def TailChunk001Sub000Block035Part006SupportExplicit : Finset ℕ :=
  ([17945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part006 : ℚ :=
  (12103307150125 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block035Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17945
    = surrogateDiagTailX0RatChunk001Sub000Block035Part006

theorem surrogateDiagonalTailChunk001Sub000Block035Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part006] using hcert

def TailChunk001Sub000Block035Part007SupportExplicit : Finset ℕ :=
  ([17947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part007 : ℚ :=
  (784769928841 : ℚ) / 9772729834111795200

def SurrogateDiagonalTailChunk001Sub000Block035Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17947
    = surrogateDiagTailX0RatChunk001Sub000Block035Part007

theorem surrogateDiagonalTailChunk001Sub000Block035Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part007] using hcert

def TailChunk001Sub000Block035Part008SupportExplicit : Finset ℕ :=
  ([17949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part008 : ℚ :=
  (37448014939 : ℚ) / 195728585313484800

def SurrogateDiagonalTailChunk001Sub000Block035Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17949
    = surrogateDiagTailX0RatChunk001Sub000Block035Part008

theorem surrogateDiagonalTailChunk001Sub000Block035Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part008] using hcert

def TailChunk001Sub000Block035Part009SupportExplicit : Finset ℕ :=
  ([17951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part009 : ℚ :=
  (18891709732825 : ℚ) / 224188269458826774528

def SurrogateDiagonalTailChunk001Sub000Block035Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17951
    = surrogateDiagTailX0RatChunk001Sub000Block035Part009

theorem surrogateDiagonalTailChunk001Sub000Block035Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part009] using hcert

def TailChunk001Sub000Block035Part010SupportExplicit : Finset ℕ :=
  ([17953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part010 : ℚ :=
  (77255502593 : ℚ) / 835767868693708800

def SurrogateDiagonalTailChunk001Sub000Block035Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17953
    = surrogateDiagTailX0RatChunk001Sub000Block035Part010

theorem surrogateDiagonalTailChunk001Sub000Block035Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part010] using hcert

def TailChunk001Sub000Block035Part011SupportExplicit : Finset ℕ :=
  ([17954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part011 : ℚ :=
  (7752940525 : ℚ) / 23344929787387008

def SurrogateDiagonalTailChunk001Sub000Block035Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17954
    = surrogateDiagTailX0RatChunk001Sub000Block035Part011

theorem surrogateDiagonalTailChunk001Sub000Block035Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part011] using hcert

def TailChunk001Sub000Block035Part012SupportExplicit : Finset ℕ :=
  ([17957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part012 : ℚ :=
  (5038341390625 : ℚ) / 64983822574744372512

def SurrogateDiagonalTailChunk001Sub000Block035Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17957
    = surrogateDiagTailX0RatChunk001Sub000Block035Part012

theorem surrogateDiagonalTailChunk001Sub000Block035Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part012] using hcert

def TailChunk001Sub000Block035Part013SupportExplicit : Finset ℕ :=
  ([17958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part013 : ℚ :=
  (85602689077 : ℚ) / 110097329238835200

def SurrogateDiagonalTailChunk001Sub000Block035Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17958
    = surrogateDiagTailX0RatChunk001Sub000Block035Part013

theorem surrogateDiagonalTailChunk001Sub000Block035Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part013] using hcert

def TailChunk001Sub000Block035Part014SupportExplicit : Finset ℕ :=
  ([17959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part014 : ℚ :=
  (5039463765625 : ℚ) / 65012779883970406962

def SurrogateDiagonalTailChunk001Sub000Block035Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17959
    = surrogateDiagTailX0RatChunk001Sub000Block035Part014

theorem surrogateDiagonalTailChunk001Sub000Block035Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part014] using hcert

def TailChunk001Sub000Block035Part015SupportExplicit : Finset ℕ :=
  ([17961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part015 : ℚ :=
  (8958673401325 : ℚ) / 51368122377458099328

def SurrogateDiagonalTailChunk001Sub000Block035Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17961
    = surrogateDiagTailX0RatChunk001Sub000Block035Part015

theorem surrogateDiagonalTailChunk001Sub000Block035Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part015] using hcert

def TailChunk001Sub000Block035Part016SupportExplicit : Finset ℕ :=
  ([17962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part016 : ℚ :=
  (222698770475 : ℚ) / 486308047104668736

def SurrogateDiagonalTailChunk001Sub000Block035Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17962
    = surrogateDiagTailX0RatChunk001Sub000Block035Part016

theorem surrogateDiagonalTailChunk001Sub000Block035Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part016] using hcert

def TailChunk001Sub000Block035Part017SupportExplicit : Finset ℕ :=
  ([17963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part017 : ℚ :=
  (614330307589 : ℚ) / 5625611457312000000

def SurrogateDiagonalTailChunk001Sub000Block035Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17963
    = surrogateDiagTailX0RatChunk001Sub000Block035Part017

theorem surrogateDiagonalTailChunk001Sub000Block035Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part017] using hcert

def TailChunk001Sub000Block035Part018SupportExplicit : Finset ℕ :=
  ([17965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part018 : ℚ :=
  (806482140625 : ℚ) / 6660274879470010368

def SurrogateDiagonalTailChunk001Sub000Block035Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17965
    = surrogateDiagTailX0RatChunk001Sub000Block035Part018

theorem surrogateDiagonalTailChunk001Sub000Block035Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part018] using hcert

def TailChunk001Sub000Block035Part019SupportExplicit : Finset ℕ :=
  ([17966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part019 : ℚ :=
  (178714424371 : ℚ) / 470119426140211200

def SurrogateDiagonalTailChunk001Sub000Block035Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17966
    = surrogateDiagTailX0RatChunk001Sub000Block035Part019

theorem surrogateDiagonalTailChunk001Sub000Block035Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part019] using hcert

def TailChunk001Sub000Block035Part020SupportExplicit : Finset ℕ :=
  ([17967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part020 : ℚ :=
  (1429886186325 : ℚ) / 7671513548501024768

def SurrogateDiagonalTailChunk001Sub000Block035Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17967
    = surrogateDiagTailX0RatChunk001Sub000Block035Part020

theorem surrogateDiagonalTailChunk001Sub000Block035Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part020] using hcert

def TailChunk001Sub000Block035Part021SupportExplicit : Finset ℕ :=
  ([17969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part021 : ℚ :=
  (180547176439 : ℚ) / 1433558974464000000

def SurrogateDiagonalTailChunk001Sub000Block035Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17969
    = surrogateDiagTailX0RatChunk001Sub000Block035Part021

theorem surrogateDiagonalTailChunk001Sub000Block035Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part021] using hcert

def TailChunk001Sub000Block035Part022SupportExplicit : Finset ℕ :=
  ([17970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part022 : ℚ :=
  (40026363475 : ℚ) / 25187681858985984

def SurrogateDiagonalTailChunk001Sub000Block035Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17970
    = surrogateDiagTailX0RatChunk001Sub000Block035Part022

theorem surrogateDiagonalTailChunk001Sub000Block035Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part022] using hcert

def TailChunk001Sub000Block035Part023SupportExplicit : Finset ℕ :=
  ([17971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part023 : ℚ :=
  (8073921025 : ℚ) / 104298763238341362

def SurrogateDiagonalTailChunk001Sub000Block035Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17971
    = surrogateDiagTailX0RatChunk001Sub000Block035Part023

theorem surrogateDiagonalTailChunk001Sub000Block035Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part023] using hcert

def TailChunk001Sub000Block035Part024SupportExplicit : Finset ℕ :=
  ([17974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block035Part024 : ℚ :=
  (158064487381 : ℚ) / 326718729975859200

def SurrogateDiagonalTailChunk001Sub000Block035Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17974
    = surrogateDiagTailX0RatChunk001Sub000Block035Part024

theorem surrogateDiagonalTailChunk001Sub000Block035Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block035Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block035Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block035Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block035Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block035Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block035HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block035Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block035Part000
    + surrogateDiagTailX0RatChunk001Sub000Block035Part001
    + surrogateDiagTailX0RatChunk001Sub000Block035Part002
    + surrogateDiagTailX0RatChunk001Sub000Block035Part003
    + surrogateDiagTailX0RatChunk001Sub000Block035Part004
    + surrogateDiagTailX0RatChunk001Sub000Block035Part005
    + surrogateDiagTailX0RatChunk001Sub000Block035Part006
    + surrogateDiagTailX0RatChunk001Sub000Block035Part007
    + surrogateDiagTailX0RatChunk001Sub000Block035Part008
    + surrogateDiagTailX0RatChunk001Sub000Block035Part009

def surrogateDiagonalTailChunk001Sub000Block035MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block035Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block035Part010
    + surrogateDiagTailX0RatChunk001Sub000Block035Part011
    + surrogateDiagTailX0RatChunk001Sub000Block035Part012
    + surrogateDiagTailX0RatChunk001Sub000Block035Part013
    + surrogateDiagTailX0RatChunk001Sub000Block035Part014
    + surrogateDiagTailX0RatChunk001Sub000Block035Part015
    + surrogateDiagTailX0RatChunk001Sub000Block035Part016
    + surrogateDiagTailX0RatChunk001Sub000Block035Part017
    + surrogateDiagTailX0RatChunk001Sub000Block035Part018
    + surrogateDiagTailX0RatChunk001Sub000Block035Part019

def surrogateDiagonalTailChunk001Sub000Block035TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block035Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block035Part020
    + surrogateDiagTailX0RatChunk001Sub000Block035Part021
    + surrogateDiagTailX0RatChunk001Sub000Block035Part022
    + surrogateDiagTailX0RatChunk001Sub000Block035Part023
    + surrogateDiagTailX0RatChunk001Sub000Block035Part024

def surrogateDiagonalTailChunk001Sub000Block035Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block035HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block035MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block035TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block035 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block035Part000
    + surrogateDiagTailX0RatChunk001Sub000Block035Part001
    + surrogateDiagTailX0RatChunk001Sub000Block035Part002
    + surrogateDiagTailX0RatChunk001Sub000Block035Part003
    + surrogateDiagTailX0RatChunk001Sub000Block035Part004
    + surrogateDiagTailX0RatChunk001Sub000Block035Part005
    + surrogateDiagTailX0RatChunk001Sub000Block035Part006
    + surrogateDiagTailX0RatChunk001Sub000Block035Part007
    + surrogateDiagTailX0RatChunk001Sub000Block035Part008
    + surrogateDiagTailX0RatChunk001Sub000Block035Part009
    + surrogateDiagTailX0RatChunk001Sub000Block035Part010
    + surrogateDiagTailX0RatChunk001Sub000Block035Part011
    + surrogateDiagTailX0RatChunk001Sub000Block035Part012
    + surrogateDiagTailX0RatChunk001Sub000Block035Part013
    + surrogateDiagTailX0RatChunk001Sub000Block035Part014
    + surrogateDiagTailX0RatChunk001Sub000Block035Part015
    + surrogateDiagTailX0RatChunk001Sub000Block035Part016
    + surrogateDiagTailX0RatChunk001Sub000Block035Part017
    + surrogateDiagTailX0RatChunk001Sub000Block035Part018
    + surrogateDiagTailX0RatChunk001Sub000Block035Part019
    + surrogateDiagTailX0RatChunk001Sub000Block035Part020
    + surrogateDiagTailX0RatChunk001Sub000Block035Part021
    + surrogateDiagTailX0RatChunk001Sub000Block035Part022
    + surrogateDiagTailX0RatChunk001Sub000Block035Part023
    + surrogateDiagTailX0RatChunk001Sub000Block035Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block035_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block035Head + surrogateDiagTailX0RatChunk001Sub000Block035Mid + surrogateDiagTailX0RatChunk001Sub000Block035Tail =
      surrogateDiagTailX0RatChunk001Sub000Block035 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block035Head surrogateDiagTailX0RatChunk001Sub000Block035Mid surrogateDiagTailX0RatChunk001Sub000Block035Tail surrogateDiagTailX0RatChunk001Sub000Block035
  ring

def SurrogateDiagonalTailChunk001Sub000Block035HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block035HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block035Head

def SurrogateDiagonalTailChunk001Sub000Block035MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block035MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block035Mid

def SurrogateDiagonalTailChunk001Sub000Block035TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block035TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block035Tail

theorem surrogateDiagonalTailChunk001Sub000Block035_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block035HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block035MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block035TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block035Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block035 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block035HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block035MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block035TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block035Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block035_eq_head_add_mid_add_tail

/-- Block 036 covers tail-support indices [10900,10925) and q from 17977 to 18015. -/

def TailChunk001Sub000Block036Part000SupportExplicit : Finset ℕ :=
  ([17977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part000 : ℚ :=
  (5049570765625 : ℚ) / 65273831373970985472

def SurrogateDiagonalTailChunk001Sub000Block036Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17977
    = surrogateDiagTailX0RatChunk001Sub000Block036Part000

theorem surrogateDiagonalTailChunk001Sub000Block036Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part000] using hcert

def TailChunk001Sub000Block036Part001SupportExplicit : Finset ℕ :=
  ([17978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part001 : ℚ :=
  (13063540329 : ℚ) / 39987686604800000

def SurrogateDiagonalTailChunk001Sub000Block036Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17978
    = surrogateDiagTailX0RatChunk001Sub000Block036Part001

theorem surrogateDiagonalTailChunk001Sub000Block036Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part001] using hcert

def TailChunk001Sub000Block036Part002SupportExplicit : Finset ℕ :=
  ([17979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part002 : ℚ :=
  (21003325531 : ℚ) / 99053969622958080

def SurrogateDiagonalTailChunk001Sub000Block036Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17979
    = surrogateDiagTailX0RatChunk001Sub000Block036Part002

theorem surrogateDiagonalTailChunk001Sub000Block036Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part002] using hcert

def TailChunk001Sub000Block036Part003SupportExplicit : Finset ℕ :=
  ([17981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part003 : ℚ :=
  (8082909025 : ℚ) / 104531119067564832

def SurrogateDiagonalTailChunk001Sub000Block036Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17981
    = surrogateDiagTailX0RatChunk001Sub000Block036Part003

theorem surrogateDiagonalTailChunk001Sub000Block036Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part003] using hcert

def TailChunk001Sub000Block036Part004SupportExplicit : Finset ℕ :=
  ([17985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part004 : ℚ :=
  (204879702751 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub000Block036Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17985
    = surrogateDiagTailX0RatChunk001Sub000Block036Part004

theorem surrogateDiagonalTailChunk001Sub000Block036Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part004] using hcert

def TailChunk001Sub000Block036Part005SupportExplicit : Finset ℕ :=
  ([17987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part005 : ℚ :=
  (5055190140625 : ℚ) / 65419199240147318802

def SurrogateDiagonalTailChunk001Sub000Block036Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17987
    = surrogateDiagTailX0RatChunk001Sub000Block036Part005

theorem surrogateDiagonalTailChunk001Sub000Block036Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part005] using hcert

def TailChunk001Sub000Block036Part006SupportExplicit : Finset ℕ :=
  ([17989] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part006 : ℚ :=
  (5056314390625 : ℚ) / 65448301925229410592

def SurrogateDiagonalTailChunk001Sub000Block036Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17989
    = surrogateDiagTailX0RatChunk001Sub000Block036Part006

theorem surrogateDiagonalTailChunk001Sub000Block036Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part006] using hcert

def TailChunk001Sub000Block036Part007SupportExplicit : Finset ℕ :=
  ([17990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part007 : ℚ :=
  (316709839225 : ℚ) / 395903350836559872

def SurrogateDiagonalTailChunk001Sub000Block036Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17990
    = surrogateDiagTailX0RatChunk001Sub000Block036Part007

theorem surrogateDiagonalTailChunk001Sub000Block036Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part007] using hcert

def TailChunk001Sub000Block036Part008SupportExplicit : Finset ℕ :=
  ([17993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part008 : ℚ :=
  (35676545125 : ℚ) / 407410036205138208

def SurrogateDiagonalTailChunk001Sub000Block036Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17993
    = surrogateDiagTailX0RatChunk001Sub000Block036Part008

theorem surrogateDiagonalTailChunk001Sub000Block036Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part008] using hcert

def TailChunk001Sub000Block036Part009SupportExplicit : Finset ℕ :=
  ([17994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part009 : ℚ :=
  (702456378175 : ℚ) / 808003727471968032

def SurrogateDiagonalTailChunk001Sub000Block036Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17994
    = surrogateDiagTailX0RatChunk001Sub000Block036Part009

theorem surrogateDiagonalTailChunk001Sub000Block036Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part009] using hcert

def TailChunk001Sub000Block036Part010SupportExplicit : Finset ℕ :=
  ([17995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part010 : ℚ :=
  (5979841861 : ℚ) / 43164283738521600

def SurrogateDiagonalTailChunk001Sub000Block036Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17995
    = surrogateDiagTailX0RatChunk001Sub000Block036Part010

theorem surrogateDiagonalTailChunk001Sub000Block036Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part010] using hcert

def TailChunk001Sub000Block036Part011SupportExplicit : Finset ℕ :=
  ([17997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part011 : ℚ :=
  (6964324921225 : ℚ) / 27838568649290416128

def SurrogateDiagonalTailChunk001Sub000Block036Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17997
    = surrogateDiagTailX0RatChunk001Sub000Block036Part011

theorem surrogateDiagonalTailChunk001Sub000Block036Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part011] using hcert

def TailChunk001Sub000Block036Part012SupportExplicit : Finset ℕ :=
  ([17998] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part012 : ℚ :=
  (1265343765625 : ℚ) / 4097800611062974002

def SurrogateDiagonalTailChunk001Sub000Block036Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17998
    = surrogateDiagTailX0RatChunk001Sub000Block036Part012

theorem surrogateDiagonalTailChunk001Sub000Block036Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part012] using hcert

def TailChunk001Sub000Block036Part013SupportExplicit : Finset ℕ :=
  ([17999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part013 : ℚ :=
  (386610741563 : ℚ) / 4711869588488601600

def SurrogateDiagonalTailChunk001Sub000Block036Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 17999
    = surrogateDiagTailX0RatChunk001Sub000Block036Part013

theorem surrogateDiagonalTailChunk001Sub000Block036Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part013] using hcert

def TailChunk001Sub000Block036Part014SupportExplicit : Finset ℕ :=
  ([18001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part014 : ℚ :=
  (6474614002725 : ℚ) / 79467652230903918976

def SurrogateDiagonalTailChunk001Sub000Block036Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18001
    = surrogateDiagTailX0RatChunk001Sub000Block036Part014

theorem surrogateDiagonalTailChunk001Sub000Block036Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part014] using hcert

def TailChunk001Sub000Block036Part015SupportExplicit : Finset ℕ :=
  ([18002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part015 : ℚ :=
  (81018001 : ℚ) / 262492488000000

def SurrogateDiagonalTailChunk001Sub000Block036Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18002
    = surrogateDiagTailX0RatChunk001Sub000Block036Part015

theorem surrogateDiagonalTailChunk001Sub000Block036Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part015] using hcert

def TailChunk001Sub000Block036Part016SupportExplicit : Finset ℕ :=
  ([18003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part016 : ℚ :=
  (168953299275 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk001Sub000Block036Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18003
    = surrogateDiagTailX0RatChunk001Sub000Block036Part016

theorem surrogateDiagonalTailChunk001Sub000Block036Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part016] using hcert

def TailChunk001Sub000Block036Part017SupportExplicit : Finset ℕ :=
  ([18005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part017 : ℚ :=
  (11889477595525 : ℚ) / 77024366778812203008

def SurrogateDiagonalTailChunk001Sub000Block036Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18005
    = surrogateDiagTailX0RatChunk001Sub000Block036Part017

theorem surrogateDiagonalTailChunk001Sub000Block036Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part017] using hcert

def TailChunk001Sub000Block036Part018SupportExplicit : Finset ℕ :=
  ([18006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part018 : ℚ :=
  (56271497249 : ℚ) / 64812960000000000

def SurrogateDiagonalTailChunk001Sub000Block036Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18006
    = surrogateDiagTailX0RatChunk001Sub000Block036Part018

theorem surrogateDiagonalTailChunk001Sub000Block036Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part018] using hcert

def TailChunk001Sub000Block036Part019SupportExplicit : Finset ℕ :=
  ([18007] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part019 : ℚ :=
  (56890180503 : ℚ) / 597088630348633600

def SurrogateDiagonalTailChunk001Sub000Block036Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18007
    = surrogateDiagTailX0RatChunk001Sub000Block036Part019

theorem surrogateDiagonalTailChunk001Sub000Block036Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part019] using hcert

def TailChunk001Sub000Block036Part020SupportExplicit : Finset ℕ :=
  ([18010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part020 : ℚ :=
  (145872692197 : ℚ) / 268792307712000000

def SurrogateDiagonalTailChunk001Sub000Block036Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18010
    = surrogateDiagTailX0RatChunk001Sub000Block036Part020

theorem surrogateDiagonalTailChunk001Sub000Block036Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part020] using hcert

def TailChunk001Sub000Block036Part021SupportExplicit : Finset ℕ :=
  ([18011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part021 : ℚ :=
  (113530145393 : ℚ) / 949428525290711040

def SurrogateDiagonalTailChunk001Sub000Block036Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18011
    = surrogateDiagTailX0RatChunk001Sub000Block036Part021

theorem surrogateDiagonalTailChunk001Sub000Block036Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part021] using hcert

def TailChunk001Sub000Block036Part022SupportExplicit : Finset ℕ :=
  ([18013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part022 : ℚ :=
  (5069815140625 : ℚ) / 65798292064780514592

def SurrogateDiagonalTailChunk001Sub000Block036Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18013
    = surrogateDiagTailX0RatChunk001Sub000Block036Part022

theorem surrogateDiagonalTailChunk001Sub000Block036Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part022] using hcert

def TailChunk001Sub000Block036Part023SupportExplicit : Finset ℕ :=
  ([18014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part023 : ℚ :=
  (1267594515625 : ℚ) / 4112393254048782162

def SurrogateDiagonalTailChunk001Sub000Block036Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18014
    = surrogateDiagTailX0RatChunk001Sub000Block036Part023

theorem surrogateDiagonalTailChunk001Sub000Block036Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part023] using hcert

def TailChunk001Sub000Block036Part024SupportExplicit : Finset ℕ :=
  ([18015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block036Part024 : ℚ :=
  (21008666417 : ℚ) / 70793035776000000

def SurrogateDiagonalTailChunk001Sub000Block036Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18015
    = surrogateDiagTailX0RatChunk001Sub000Block036Part024

theorem surrogateDiagonalTailChunk001Sub000Block036Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block036Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block036Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block036Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block036Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block036Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block036HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block036Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block036Part000
    + surrogateDiagTailX0RatChunk001Sub000Block036Part001
    + surrogateDiagTailX0RatChunk001Sub000Block036Part002
    + surrogateDiagTailX0RatChunk001Sub000Block036Part003
    + surrogateDiagTailX0RatChunk001Sub000Block036Part004
    + surrogateDiagTailX0RatChunk001Sub000Block036Part005
    + surrogateDiagTailX0RatChunk001Sub000Block036Part006
    + surrogateDiagTailX0RatChunk001Sub000Block036Part007
    + surrogateDiagTailX0RatChunk001Sub000Block036Part008
    + surrogateDiagTailX0RatChunk001Sub000Block036Part009

def surrogateDiagonalTailChunk001Sub000Block036MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block036Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block036Part010
    + surrogateDiagTailX0RatChunk001Sub000Block036Part011
    + surrogateDiagTailX0RatChunk001Sub000Block036Part012
    + surrogateDiagTailX0RatChunk001Sub000Block036Part013
    + surrogateDiagTailX0RatChunk001Sub000Block036Part014
    + surrogateDiagTailX0RatChunk001Sub000Block036Part015
    + surrogateDiagTailX0RatChunk001Sub000Block036Part016
    + surrogateDiagTailX0RatChunk001Sub000Block036Part017
    + surrogateDiagTailX0RatChunk001Sub000Block036Part018
    + surrogateDiagTailX0RatChunk001Sub000Block036Part019

def surrogateDiagonalTailChunk001Sub000Block036TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block036Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block036Part020
    + surrogateDiagTailX0RatChunk001Sub000Block036Part021
    + surrogateDiagTailX0RatChunk001Sub000Block036Part022
    + surrogateDiagTailX0RatChunk001Sub000Block036Part023
    + surrogateDiagTailX0RatChunk001Sub000Block036Part024

def surrogateDiagonalTailChunk001Sub000Block036Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block036HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block036MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block036TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block036 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block036Part000
    + surrogateDiagTailX0RatChunk001Sub000Block036Part001
    + surrogateDiagTailX0RatChunk001Sub000Block036Part002
    + surrogateDiagTailX0RatChunk001Sub000Block036Part003
    + surrogateDiagTailX0RatChunk001Sub000Block036Part004
    + surrogateDiagTailX0RatChunk001Sub000Block036Part005
    + surrogateDiagTailX0RatChunk001Sub000Block036Part006
    + surrogateDiagTailX0RatChunk001Sub000Block036Part007
    + surrogateDiagTailX0RatChunk001Sub000Block036Part008
    + surrogateDiagTailX0RatChunk001Sub000Block036Part009
    + surrogateDiagTailX0RatChunk001Sub000Block036Part010
    + surrogateDiagTailX0RatChunk001Sub000Block036Part011
    + surrogateDiagTailX0RatChunk001Sub000Block036Part012
    + surrogateDiagTailX0RatChunk001Sub000Block036Part013
    + surrogateDiagTailX0RatChunk001Sub000Block036Part014
    + surrogateDiagTailX0RatChunk001Sub000Block036Part015
    + surrogateDiagTailX0RatChunk001Sub000Block036Part016
    + surrogateDiagTailX0RatChunk001Sub000Block036Part017
    + surrogateDiagTailX0RatChunk001Sub000Block036Part018
    + surrogateDiagTailX0RatChunk001Sub000Block036Part019
    + surrogateDiagTailX0RatChunk001Sub000Block036Part020
    + surrogateDiagTailX0RatChunk001Sub000Block036Part021
    + surrogateDiagTailX0RatChunk001Sub000Block036Part022
    + surrogateDiagTailX0RatChunk001Sub000Block036Part023
    + surrogateDiagTailX0RatChunk001Sub000Block036Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block036_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block036Head + surrogateDiagTailX0RatChunk001Sub000Block036Mid + surrogateDiagTailX0RatChunk001Sub000Block036Tail =
      surrogateDiagTailX0RatChunk001Sub000Block036 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block036Head surrogateDiagTailX0RatChunk001Sub000Block036Mid surrogateDiagTailX0RatChunk001Sub000Block036Tail surrogateDiagTailX0RatChunk001Sub000Block036
  ring

def SurrogateDiagonalTailChunk001Sub000Block036HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block036HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block036Head

def SurrogateDiagonalTailChunk001Sub000Block036MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block036MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block036Mid

def SurrogateDiagonalTailChunk001Sub000Block036TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block036TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block036Tail

theorem surrogateDiagonalTailChunk001Sub000Block036_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block036HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block036MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block036TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block036Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block036 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block036HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block036MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block036TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block036Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block036_eq_head_add_mid_add_tail

/-- Block 037 covers tail-support indices [10925,10950) and q from 18017 to 18058. -/

def TailChunk001Sub000Block037Part000SupportExplicit : Finset ℕ :=
  ([18017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part000 : ℚ :=
  (9699158711975 : ℚ) / 118767920337993858624

def SurrogateDiagonalTailChunk001Sub000Block037Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18017
    = surrogateDiagTailX0RatChunk001Sub000Block037Part000

theorem surrogateDiagonalTailChunk001Sub000Block037Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part000] using hcert

def TailChunk001Sub000Block037Part001SupportExplicit : Finset ℕ :=
  ([18019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part001 : ℚ :=
  (356992329925 : ℚ) / 4338985303884229632

def SurrogateDiagonalTailChunk001Sub000Block037Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18019
    = surrogateDiagTailX0RatChunk001Sub000Block037Part001

theorem surrogateDiagonalTailChunk001Sub000Block037Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part001] using hcert

def TailChunk001Sub000Block037Part002SupportExplicit : Finset ℕ :=
  ([18021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part002 : ℚ :=
  (74534160325 : ℚ) / 430232072575713408

def SurrogateDiagonalTailChunk001Sub000Block037Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18021
    = surrogateDiagTailX0RatChunk001Sub000Block037Part002

theorem surrogateDiagonalTailChunk001Sub000Block037Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part002] using hcert

def TailChunk001Sub000Block037Part003SupportExplicit : Finset ℕ :=
  ([18022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part003 : ℚ :=
  (2029953025 : ℚ) / 6591526677737202

def SurrogateDiagonalTailChunk001Sub000Block037Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18022
    = surrogateDiagTailX0RatChunk001Sub000Block037Part003

theorem surrogateDiagonalTailChunk001Sub000Block037Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part003] using hcert

def TailChunk001Sub000Block037Part004SupportExplicit : Finset ℕ :=
  ([18023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part004 : ℚ :=
  (1092066336725 : ℚ) / 13597819502907442176

def SurrogateDiagonalTailChunk001Sub000Block037Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18023
    = surrogateDiagTailX0RatChunk001Sub000Block037Part004

theorem surrogateDiagonalTailChunk001Sub000Block037Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part004] using hcert

def TailChunk001Sub000Block037Part005SupportExplicit : Finset ℕ :=
  ([18026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part005 : ℚ :=
  (1269283890625 : ℚ) / 4123363286648738592

def SurrogateDiagonalTailChunk001Sub000Block037Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18026
    = surrogateDiagTailX0RatChunk001Sub000Block037Part005

theorem surrogateDiagonalTailChunk001Sub000Block037Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part005] using hcert

def TailChunk001Sub000Block037Part006SupportExplicit : Finset ℕ :=
  ([18030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part006 : ℚ :=
  (4656221519 : ℚ) / 2949709824000000

def SurrogateDiagonalTailChunk001Sub000Block037Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18030
    = surrogateDiagTailX0RatChunk001Sub000Block037Part006

theorem surrogateDiagonalTailChunk001Sub000Block037Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part006] using hcert

def TailChunk001Sub000Block037Part007SupportExplicit : Finset ℕ :=
  ([18031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part007 : ℚ :=
  (1749894057875 : ℚ) / 16252842985559949312

def SurrogateDiagonalTailChunk001Sub000Block037Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18031
    = surrogateDiagTailX0RatChunk001Sub000Block037Part007

theorem surrogateDiagonalTailChunk001Sub000Block037Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part007] using hcert

def TailChunk001Sub000Block037Part008SupportExplicit : Finset ℕ :=
  ([18033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part008 : ℚ :=
  (361225975957 : ℚ) / 2087876090135683200

def SurrogateDiagonalTailChunk001Sub000Block037Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18033
    = surrogateDiagTailX0RatChunk001Sub000Block037Part008

theorem surrogateDiagonalTailChunk001Sub000Block037Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part008] using hcert

def TailChunk001Sub000Block037Part009SupportExplicit : Finset ℕ :=
  ([18034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part009 : ℚ :=
  (97657583 : ℚ) / 300241459784700

def SurrogateDiagonalTailChunk001Sub000Block037Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18034
    = surrogateDiagTailX0RatChunk001Sub000Block037Part009

theorem surrogateDiagonalTailChunk001Sub000Block037Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part009] using hcert

def TailChunk001Sub000Block037Part010SupportExplicit : Finset ℕ :=
  ([18035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part010 : ℚ :=
  (13818489031525 : ℚ) / 108235496512633817088

def SurrogateDiagonalTailChunk001Sub000Block037Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18035
    = surrogateDiagTailX0RatChunk001Sub000Block037Part010

theorem surrogateDiagonalTailChunk001Sub000Block037Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part010] using hcert

def TailChunk001Sub000Block037Part011SupportExplicit : Finset ℕ :=
  ([18037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part011 : ℚ :=
  (11429211643 : ℚ) / 8275423758857011200

def SurrogateDiagonalTailChunk001Sub000Block037Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18037
    = surrogateDiagTailX0RatChunk001Sub000Block037Part011

theorem surrogateDiagonalTailChunk001Sub000Block037Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part011] using hcert

def TailChunk001Sub000Block037Part012SupportExplicit : Finset ℕ :=
  ([18038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part012 : ℚ :=
  (2090837723 : ℚ) / 283880626660377600

def SurrogateDiagonalTailChunk001Sub000Block037Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18038
    = surrogateDiagTailX0RatChunk001Sub000Block037Part012

theorem surrogateDiagonalTailChunk001Sub000Block037Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part012] using hcert

def TailChunk001Sub000Block037Part013SupportExplicit : Finset ℕ :=
  ([18039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part013 : ℚ :=
  (371867847025 : ℚ) / 28099655432333641728

def SurrogateDiagonalTailChunk001Sub000Block037Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18039
    = surrogateDiagTailX0RatChunk001Sub000Block037Part013

theorem surrogateDiagonalTailChunk001Sub000Block037Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part013] using hcert

def TailChunk001Sub000Block037Part014SupportExplicit : Finset ℕ :=
  ([18041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block037Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18041
    = surrogateDiagTailX0RatChunk001Sub000Block037Part014

theorem surrogateDiagonalTailChunk001Sub000Block037Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part014] using hcert

def TailChunk001Sub000Block037Part015SupportExplicit : Finset ℕ :=
  ([18042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part015 : ℚ :=
  (2979370583 : ℚ) / 13762166154854400

def SurrogateDiagonalTailChunk001Sub000Block037Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18042
    = surrogateDiagTailX0RatChunk001Sub000Block037Part015

theorem surrogateDiagonalTailChunk001Sub000Block037Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part015] using hcert

def TailChunk001Sub000Block037Part016SupportExplicit : Finset ℕ :=
  ([18043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block037Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18043
    = surrogateDiagTailX0RatChunk001Sub000Block037Part016

theorem surrogateDiagonalTailChunk001Sub000Block037Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part016] using hcert

def TailChunk001Sub000Block037Part017SupportExplicit : Finset ℕ :=
  ([18046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part017 : ℚ :=
  (416361591925 : ℚ) / 8918571789927088128

def SurrogateDiagonalTailChunk001Sub000Block037Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18046
    = surrogateDiagTailX0RatChunk001Sub000Block037Part017

theorem surrogateDiagonalTailChunk001Sub000Block037Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part017] using hcert

def TailChunk001Sub000Block037Part018SupportExplicit : Finset ℕ :=
  ([18047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block037Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18047
    = surrogateDiagTailX0RatChunk001Sub000Block037Part018

theorem surrogateDiagonalTailChunk001Sub000Block037Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part018] using hcert

def TailChunk001Sub000Block037Part019SupportExplicit : Finset ℕ :=
  ([18049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block037Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18049
    = surrogateDiagTailX0RatChunk001Sub000Block037Part019

theorem surrogateDiagonalTailChunk001Sub000Block037Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part019] using hcert

def TailChunk001Sub000Block037Part020SupportExplicit : Finset ℕ :=
  ([18051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part020 : ℚ :=
  (195262651 : ℚ) / 20317925505346560

def SurrogateDiagonalTailChunk001Sub000Block037Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18051
    = surrogateDiagTailX0RatChunk001Sub000Block037Part020

theorem surrogateDiagonalTailChunk001Sub000Block037Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part020] using hcert

def TailChunk001Sub000Block037Part021SupportExplicit : Finset ℕ :=
  ([18053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part021 : ℚ :=
  (416234582075 : ℚ) / 71570411926932078144

def SurrogateDiagonalTailChunk001Sub000Block037Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18053
    = surrogateDiagTailX0RatChunk001Sub000Block037Part021

theorem surrogateDiagonalTailChunk001Sub000Block037Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part021] using hcert

def TailChunk001Sub000Block037Part022SupportExplicit : Finset ℕ :=
  ([18055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part022 : ℚ :=
  (88244168975 : ℚ) / 8073526139929755648

def SurrogateDiagonalTailChunk001Sub000Block037Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18055
    = surrogateDiagTailX0RatChunk001Sub000Block037Part022

theorem surrogateDiagonalTailChunk001Sub000Block037Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part022] using hcert

def TailChunk001Sub000Block037Part023SupportExplicit : Finset ℕ :=
  ([18057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part023 : ℚ :=
  (34931412025 : ℚ) / 4199496450437578752

def SurrogateDiagonalTailChunk001Sub000Block037Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18057
    = surrogateDiagTailX0RatChunk001Sub000Block037Part023

theorem surrogateDiagonalTailChunk001Sub000Block037Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part023] using hcert

def TailChunk001Sub000Block037Part024SupportExplicit : Finset ℕ :=
  ([18058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block037Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block037Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18058
    = surrogateDiagTailX0RatChunk001Sub000Block037Part024

theorem surrogateDiagonalTailChunk001Sub000Block037Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block037Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block037Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block037Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block037Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block037Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block037HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block037Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block037Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block037Part000
    + surrogateDiagTailX0RatChunk001Sub000Block037Part001
    + surrogateDiagTailX0RatChunk001Sub000Block037Part002
    + surrogateDiagTailX0RatChunk001Sub000Block037Part003
    + surrogateDiagTailX0RatChunk001Sub000Block037Part004
    + surrogateDiagTailX0RatChunk001Sub000Block037Part005
    + surrogateDiagTailX0RatChunk001Sub000Block037Part006
    + surrogateDiagTailX0RatChunk001Sub000Block037Part007
    + surrogateDiagTailX0RatChunk001Sub000Block037Part008
    + surrogateDiagTailX0RatChunk001Sub000Block037Part009

def surrogateDiagonalTailChunk001Sub000Block037MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block037Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block037Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block037Part010
    + surrogateDiagTailX0RatChunk001Sub000Block037Part011
    + surrogateDiagTailX0RatChunk001Sub000Block037Part012
    + surrogateDiagTailX0RatChunk001Sub000Block037Part013
    + surrogateDiagTailX0RatChunk001Sub000Block037Part014
    + surrogateDiagTailX0RatChunk001Sub000Block037Part015
    + surrogateDiagTailX0RatChunk001Sub000Block037Part016
    + surrogateDiagTailX0RatChunk001Sub000Block037Part017
    + surrogateDiagTailX0RatChunk001Sub000Block037Part018
    + surrogateDiagTailX0RatChunk001Sub000Block037Part019

def surrogateDiagonalTailChunk001Sub000Block037TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block037Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block037Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block037Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block037Part020
    + surrogateDiagTailX0RatChunk001Sub000Block037Part021
    + surrogateDiagTailX0RatChunk001Sub000Block037Part022
    + surrogateDiagTailX0RatChunk001Sub000Block037Part023
    + surrogateDiagTailX0RatChunk001Sub000Block037Part024

def surrogateDiagonalTailChunk001Sub000Block037Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block037HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block037MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block037TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block037 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block037Part000
    + surrogateDiagTailX0RatChunk001Sub000Block037Part001
    + surrogateDiagTailX0RatChunk001Sub000Block037Part002
    + surrogateDiagTailX0RatChunk001Sub000Block037Part003
    + surrogateDiagTailX0RatChunk001Sub000Block037Part004
    + surrogateDiagTailX0RatChunk001Sub000Block037Part005
    + surrogateDiagTailX0RatChunk001Sub000Block037Part006
    + surrogateDiagTailX0RatChunk001Sub000Block037Part007
    + surrogateDiagTailX0RatChunk001Sub000Block037Part008
    + surrogateDiagTailX0RatChunk001Sub000Block037Part009
    + surrogateDiagTailX0RatChunk001Sub000Block037Part010
    + surrogateDiagTailX0RatChunk001Sub000Block037Part011
    + surrogateDiagTailX0RatChunk001Sub000Block037Part012
    + surrogateDiagTailX0RatChunk001Sub000Block037Part013
    + surrogateDiagTailX0RatChunk001Sub000Block037Part014
    + surrogateDiagTailX0RatChunk001Sub000Block037Part015
    + surrogateDiagTailX0RatChunk001Sub000Block037Part016
    + surrogateDiagTailX0RatChunk001Sub000Block037Part017
    + surrogateDiagTailX0RatChunk001Sub000Block037Part018
    + surrogateDiagTailX0RatChunk001Sub000Block037Part019
    + surrogateDiagTailX0RatChunk001Sub000Block037Part020
    + surrogateDiagTailX0RatChunk001Sub000Block037Part021
    + surrogateDiagTailX0RatChunk001Sub000Block037Part022
    + surrogateDiagTailX0RatChunk001Sub000Block037Part023
    + surrogateDiagTailX0RatChunk001Sub000Block037Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block037_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block037Head + surrogateDiagTailX0RatChunk001Sub000Block037Mid + surrogateDiagTailX0RatChunk001Sub000Block037Tail =
      surrogateDiagTailX0RatChunk001Sub000Block037 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block037Head surrogateDiagTailX0RatChunk001Sub000Block037Mid surrogateDiagTailX0RatChunk001Sub000Block037Tail surrogateDiagTailX0RatChunk001Sub000Block037
  ring

def SurrogateDiagonalTailChunk001Sub000Block037HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block037HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block037Head

def SurrogateDiagonalTailChunk001Sub000Block037MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block037MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block037Mid

def SurrogateDiagonalTailChunk001Sub000Block037TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block037TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block037Tail

theorem surrogateDiagonalTailChunk001Sub000Block037_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block037HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block037MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block037TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block037Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block037 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block037HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block037MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block037TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block037Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block037_eq_head_add_mid_add_tail

/-- Block 038 covers tail-support indices [10950,10975) and q from 18059 to 18098. -/

def TailChunk001Sub000Block038Part000SupportExplicit : Finset ℕ :=
  ([18059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18059
    = surrogateDiagTailX0RatChunk001Sub000Block038Part000

theorem surrogateDiagonalTailChunk001Sub000Block038Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part000] using hcert

def TailChunk001Sub000Block038Part001SupportExplicit : Finset ℕ :=
  ([18061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18061
    = surrogateDiagTailX0RatChunk001Sub000Block038Part001

theorem surrogateDiagonalTailChunk001Sub000Block038Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part001] using hcert

def TailChunk001Sub000Block038Part002SupportExplicit : Finset ℕ :=
  ([18062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part002 : ℚ :=
  (1020098977 : ℚ) / 45221218435200000

def SurrogateDiagonalTailChunk001Sub000Block038Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18062
    = surrogateDiagTailX0RatChunk001Sub000Block038Part002

theorem surrogateDiagonalTailChunk001Sub000Block038Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part002] using hcert

def TailChunk001Sub000Block038Part003SupportExplicit : Finset ℕ :=
  ([18065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part003 : ℚ :=
  (816659735875 : ℚ) / 108957665795843063808

def SurrogateDiagonalTailChunk001Sub000Block038Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18065
    = surrogateDiagTailX0RatChunk001Sub000Block038Part003

theorem surrogateDiagonalTailChunk001Sub000Block038Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part003] using hcert

def TailChunk001Sub000Block038Part004SupportExplicit : Finset ℕ :=
  ([18066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part004 : ℚ :=
  (323932207 : ℚ) / 1876613236397760

def SurrogateDiagonalTailChunk001Sub000Block038Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18066
    = surrogateDiagTailX0RatChunk001Sub000Block038Part004

theorem surrogateDiagonalTailChunk001Sub000Block038Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part004] using hcert

def TailChunk001Sub000Block038Part005SupportExplicit : Finset ℕ :=
  ([18067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part005 : ℚ :=
  (486109598225 : ℚ) / 59726171739556675584

def SurrogateDiagonalTailChunk001Sub000Block038Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18067
    = surrogateDiagTailX0RatChunk001Sub000Block038Part005

theorem surrogateDiagonalTailChunk001Sub000Block038Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part005] using hcert

def TailChunk001Sub000Block038Part006SupportExplicit : Finset ℕ :=
  ([18069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part006 : ℚ :=
  (111747586775 : ℚ) / 20938964315118649344

def SurrogateDiagonalTailChunk001Sub000Block038Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18069
    = surrogateDiagTailX0RatChunk001Sub000Block038Part006

theorem surrogateDiagonalTailChunk001Sub000Block038Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part006] using hcert

def TailChunk001Sub000Block038Part007SupportExplicit : Finset ℕ :=
  ([18070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part007 : ℚ :=
  (693212093275 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk001Sub000Block038Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18070
    = surrogateDiagTailX0RatChunk001Sub000Block038Part007

theorem surrogateDiagonalTailChunk001Sub000Block038Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part007] using hcert

def TailChunk001Sub000Block038Part008SupportExplicit : Finset ℕ :=
  ([18071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part008 : ℚ :=
  (357167898025 : ℚ) / 208451419300440834048

def SurrogateDiagonalTailChunk001Sub000Block038Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18071
    = surrogateDiagTailX0RatChunk001Sub000Block038Part008

theorem surrogateDiagonalTailChunk001Sub000Block038Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part008] using hcert

def TailChunk001Sub000Block038Part009SupportExplicit : Finset ℕ :=
  ([18073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part009 : ℚ :=
  (4747244129 : ℚ) / 987265573632000000

def SurrogateDiagonalTailChunk001Sub000Block038Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18073
    = surrogateDiagTailX0RatChunk001Sub000Block038Part009

theorem surrogateDiagonalTailChunk001Sub000Block038Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part009] using hcert

def TailChunk001Sub000Block038Part010SupportExplicit : Finset ℕ :=
  ([18074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part010 : ℚ :=
  (16705992733 : ℚ) / 358963832186755200

def SurrogateDiagonalTailChunk001Sub000Block038Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18074
    = surrogateDiagTailX0RatChunk001Sub000Block038Part010

theorem surrogateDiagonalTailChunk001Sub000Block038Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part010] using hcert

def TailChunk001Sub000Block038Part011SupportExplicit : Finset ℕ :=
  ([18077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18077
    = surrogateDiagTailX0RatChunk001Sub000Block038Part011

theorem surrogateDiagonalTailChunk001Sub000Block038Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part011] using hcert

def TailChunk001Sub000Block038Part012SupportExplicit : Finset ℕ :=
  ([18078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part012 : ℚ :=
  (4447767001 : ℚ) / 10707077972997120

def SurrogateDiagonalTailChunk001Sub000Block038Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18078
    = surrogateDiagTailX0RatChunk001Sub000Block038Part012

theorem surrogateDiagonalTailChunk001Sub000Block038Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part012] using hcert

def TailChunk001Sub000Block038Part013SupportExplicit : Finset ℕ :=
  ([18079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part013 : ℚ :=
  (1156025559 : ℚ) / 3346922103904000000

def SurrogateDiagonalTailChunk001Sub000Block038Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18079
    = surrogateDiagTailX0RatChunk001Sub000Block038Part013

theorem surrogateDiagonalTailChunk001Sub000Block038Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part013] using hcert

def TailChunk001Sub000Block038Part014SupportExplicit : Finset ℕ :=
  ([18082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18082
    = surrogateDiagTailX0RatChunk001Sub000Block038Part014

theorem surrogateDiagonalTailChunk001Sub000Block038Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part014] using hcert

def TailChunk001Sub000Block038Part015SupportExplicit : Finset ℕ :=
  ([18085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part015 : ℚ :=
  (272822245125 : ℚ) / 36480371865142951936

def SurrogateDiagonalTailChunk001Sub000Block038Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18085
    = surrogateDiagTailX0RatChunk001Sub000Block038Part015

theorem surrogateDiagonalTailChunk001Sub000Block038Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part015] using hcert

def TailChunk001Sub000Block038Part016SupportExplicit : Finset ℕ :=
  ([18086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18086
    = surrogateDiagTailX0RatChunk001Sub000Block038Part016

theorem surrogateDiagonalTailChunk001Sub000Block038Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part016] using hcert

def TailChunk001Sub000Block038Part017SupportExplicit : Finset ℕ :=
  ([18087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part017 : ℚ :=
  (35494906825 : ℚ) / 825391214898092832

def SurrogateDiagonalTailChunk001Sub000Block038Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18087
    = surrogateDiagTailX0RatChunk001Sub000Block038Part017

theorem surrogateDiagonalTailChunk001Sub000Block038Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part017] using hcert

def TailChunk001Sub000Block038Part018SupportExplicit : Finset ℕ :=
  ([18089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18089
    = surrogateDiagTailX0RatChunk001Sub000Block038Part018

theorem surrogateDiagonalTailChunk001Sub000Block038Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part018] using hcert

def TailChunk001Sub000Block038Part019SupportExplicit : Finset ℕ :=
  ([18091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part019 : ℚ :=
  (47722947875 : ℚ) / 125058916590299587584

def SurrogateDiagonalTailChunk001Sub000Block038Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18091
    = surrogateDiagTailX0RatChunk001Sub000Block038Part019

theorem surrogateDiagonalTailChunk001Sub000Block038Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part019] using hcert

def TailChunk001Sub000Block038Part020SupportExplicit : Finset ℕ :=
  ([18093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part020 : ℚ :=
  (62405316575 : ℚ) / 1285625275224956928

def SurrogateDiagonalTailChunk001Sub000Block038Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18093
    = surrogateDiagTailX0RatChunk001Sub000Block038Part020

theorem surrogateDiagonalTailChunk001Sub000Block038Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part020] using hcert

def TailChunk001Sub000Block038Part021SupportExplicit : Finset ℕ :=
  ([18094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part021 : ℚ :=
  (58755122875 : ℚ) / 15380742109709518848

def SurrogateDiagonalTailChunk001Sub000Block038Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18094
    = surrogateDiagTailX0RatChunk001Sub000Block038Part021

theorem surrogateDiagonalTailChunk001Sub000Block038Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part021] using hcert

def TailChunk001Sub000Block038Part022SupportExplicit : Finset ℕ :=
  ([18095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part022 : ℚ :=
  (55071192583 : ℚ) / 1485809544344371200

def SurrogateDiagonalTailChunk001Sub000Block038Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18095
    = surrogateDiagTailX0RatChunk001Sub000Block038Part022

theorem surrogateDiagonalTailChunk001Sub000Block038Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part022] using hcert

def TailChunk001Sub000Block038Part023SupportExplicit : Finset ℕ :=
  ([18097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18097
    = surrogateDiagTailX0RatChunk001Sub000Block038Part023

theorem surrogateDiagonalTailChunk001Sub000Block038Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part023] using hcert

def TailChunk001Sub000Block038Part024SupportExplicit : Finset ℕ :=
  ([18098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block038Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block038Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18098
    = surrogateDiagTailX0RatChunk001Sub000Block038Part024

theorem surrogateDiagonalTailChunk001Sub000Block038Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block038Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block038Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block038Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block038Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block038Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block038HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block038Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block038Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block038Part000
    + surrogateDiagTailX0RatChunk001Sub000Block038Part001
    + surrogateDiagTailX0RatChunk001Sub000Block038Part002
    + surrogateDiagTailX0RatChunk001Sub000Block038Part003
    + surrogateDiagTailX0RatChunk001Sub000Block038Part004
    + surrogateDiagTailX0RatChunk001Sub000Block038Part005
    + surrogateDiagTailX0RatChunk001Sub000Block038Part006
    + surrogateDiagTailX0RatChunk001Sub000Block038Part007
    + surrogateDiagTailX0RatChunk001Sub000Block038Part008
    + surrogateDiagTailX0RatChunk001Sub000Block038Part009

def surrogateDiagonalTailChunk001Sub000Block038MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block038Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block038Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block038Part010
    + surrogateDiagTailX0RatChunk001Sub000Block038Part011
    + surrogateDiagTailX0RatChunk001Sub000Block038Part012
    + surrogateDiagTailX0RatChunk001Sub000Block038Part013
    + surrogateDiagTailX0RatChunk001Sub000Block038Part014
    + surrogateDiagTailX0RatChunk001Sub000Block038Part015
    + surrogateDiagTailX0RatChunk001Sub000Block038Part016
    + surrogateDiagTailX0RatChunk001Sub000Block038Part017
    + surrogateDiagTailX0RatChunk001Sub000Block038Part018
    + surrogateDiagTailX0RatChunk001Sub000Block038Part019

def surrogateDiagonalTailChunk001Sub000Block038TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block038Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block038Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block038Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block038Part020
    + surrogateDiagTailX0RatChunk001Sub000Block038Part021
    + surrogateDiagTailX0RatChunk001Sub000Block038Part022
    + surrogateDiagTailX0RatChunk001Sub000Block038Part023
    + surrogateDiagTailX0RatChunk001Sub000Block038Part024

def surrogateDiagonalTailChunk001Sub000Block038Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block038HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block038MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block038TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block038 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block038Part000
    + surrogateDiagTailX0RatChunk001Sub000Block038Part001
    + surrogateDiagTailX0RatChunk001Sub000Block038Part002
    + surrogateDiagTailX0RatChunk001Sub000Block038Part003
    + surrogateDiagTailX0RatChunk001Sub000Block038Part004
    + surrogateDiagTailX0RatChunk001Sub000Block038Part005
    + surrogateDiagTailX0RatChunk001Sub000Block038Part006
    + surrogateDiagTailX0RatChunk001Sub000Block038Part007
    + surrogateDiagTailX0RatChunk001Sub000Block038Part008
    + surrogateDiagTailX0RatChunk001Sub000Block038Part009
    + surrogateDiagTailX0RatChunk001Sub000Block038Part010
    + surrogateDiagTailX0RatChunk001Sub000Block038Part011
    + surrogateDiagTailX0RatChunk001Sub000Block038Part012
    + surrogateDiagTailX0RatChunk001Sub000Block038Part013
    + surrogateDiagTailX0RatChunk001Sub000Block038Part014
    + surrogateDiagTailX0RatChunk001Sub000Block038Part015
    + surrogateDiagTailX0RatChunk001Sub000Block038Part016
    + surrogateDiagTailX0RatChunk001Sub000Block038Part017
    + surrogateDiagTailX0RatChunk001Sub000Block038Part018
    + surrogateDiagTailX0RatChunk001Sub000Block038Part019
    + surrogateDiagTailX0RatChunk001Sub000Block038Part020
    + surrogateDiagTailX0RatChunk001Sub000Block038Part021
    + surrogateDiagTailX0RatChunk001Sub000Block038Part022
    + surrogateDiagTailX0RatChunk001Sub000Block038Part023
    + surrogateDiagTailX0RatChunk001Sub000Block038Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block038_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block038Head + surrogateDiagTailX0RatChunk001Sub000Block038Mid + surrogateDiagTailX0RatChunk001Sub000Block038Tail =
      surrogateDiagTailX0RatChunk001Sub000Block038 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block038Head surrogateDiagTailX0RatChunk001Sub000Block038Mid surrogateDiagTailX0RatChunk001Sub000Block038Tail surrogateDiagTailX0RatChunk001Sub000Block038
  ring

def SurrogateDiagonalTailChunk001Sub000Block038HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block038HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block038Head

def SurrogateDiagonalTailChunk001Sub000Block038MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block038MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block038Mid

def SurrogateDiagonalTailChunk001Sub000Block038TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block038TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block038Tail

theorem surrogateDiagonalTailChunk001Sub000Block038_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block038HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block038MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block038TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block038Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block038 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block038HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block038MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block038TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block038Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block038_eq_head_add_mid_add_tail

/-- Block 039 covers tail-support indices [10975,11000) and q from 18101 to 18139. -/

def TailChunk001Sub000Block039Part000SupportExplicit : Finset ℕ :=
  ([18101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part000 : ℚ :=
  (238306545475 : ℚ) / 223567034585858206848

def SurrogateDiagonalTailChunk001Sub000Block039Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18101
    = surrogateDiagTailX0RatChunk001Sub000Block039Part000

theorem surrogateDiagonalTailChunk001Sub000Block039Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part000] using hcert

def TailChunk001Sub000Block039Part001SupportExplicit : Finset ℕ :=
  ([18102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part001 : ℚ :=
  (266214211 : ℚ) / 437694049305600

def SurrogateDiagonalTailChunk001Sub000Block039Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18102
    = surrogateDiagTailX0RatChunk001Sub000Block039Part001

theorem surrogateDiagonalTailChunk001Sub000Block039Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part001] using hcert

def TailChunk001Sub000Block039Part002SupportExplicit : Finset ℕ :=
  ([18103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part002 : ℚ :=
  (23049209 : ℚ) / 38430906852441600

def SurrogateDiagonalTailChunk001Sub000Block039Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18103
    = surrogateDiagTailX0RatChunk001Sub000Block039Part002

theorem surrogateDiagonalTailChunk001Sub000Block039Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part002] using hcert

def TailChunk001Sub000Block039Part003SupportExplicit : Finset ℕ :=
  ([18105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part003 : ℚ :=
  (12892082811 : ℚ) / 107440405426995200

def SurrogateDiagonalTailChunk001Sub000Block039Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18105
    = surrogateDiagTailX0RatChunk001Sub000Block039Part003

theorem surrogateDiagonalTailChunk001Sub000Block039Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part003] using hcert

def TailChunk001Sub000Block039Part004SupportExplicit : Finset ℕ :=
  ([18106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part004 : ℚ :=
  (1025020039 : ℚ) / 45664017762957120

def SurrogateDiagonalTailChunk001Sub000Block039Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18106
    = surrogateDiagTailX0RatChunk001Sub000Block039Part004

theorem surrogateDiagonalTailChunk001Sub000Block039Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part004] using hcert

def TailChunk001Sub000Block039Part005SupportExplicit : Finset ℕ :=
  ([18107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part005 : ℚ :=
  (12025666325 : ℚ) / 8983662566687649792

def SurrogateDiagonalTailChunk001Sub000Block039Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18107
    = surrogateDiagTailX0RatChunk001Sub000Block039Part005

theorem surrogateDiagonalTailChunk001Sub000Block039Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part005] using hcert

def TailChunk001Sub000Block039Part006SupportExplicit : Finset ℕ :=
  ([18109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part006 : ℚ :=
  (1127363397475 : ℚ) / 103280327322735771648

def SurrogateDiagonalTailChunk001Sub000Block039Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18109
    = surrogateDiagTailX0RatChunk001Sub000Block039Part006

theorem surrogateDiagonalTailChunk001Sub000Block039Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part006] using hcert

def TailChunk001Sub000Block039Part007SupportExplicit : Finset ℕ :=
  ([18110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part007 : ℚ :=
  (16427247169 : ℚ) / 274815431071795200

def SurrogateDiagonalTailChunk001Sub000Block039Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18110
    = surrogateDiagTailX0RatChunk001Sub000Block039Part007

theorem surrogateDiagonalTailChunk001Sub000Block039Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part007] using hcert

def TailChunk001Sub000Block039Part008SupportExplicit : Finset ℕ :=
  ([18111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part008 : ℚ :=
  (284713254575 : ℚ) / 6638252672175503616

def SurrogateDiagonalTailChunk001Sub000Block039Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18111
    = surrogateDiagTailX0RatChunk001Sub000Block039Part008

theorem surrogateDiagonalTailChunk001Sub000Block039Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part008] using hcert

def TailChunk001Sub000Block039Part009SupportExplicit : Finset ℕ :=
  ([18113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part009 : ℚ :=
  (18588757375 : ℚ) / 41349788134041855168

def SurrogateDiagonalTailChunk001Sub000Block039Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18113
    = surrogateDiagTailX0RatChunk001Sub000Block039Part009

theorem surrogateDiagonalTailChunk001Sub000Block039Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part009] using hcert

def TailChunk001Sub000Block039Part010SupportExplicit : Finset ℕ :=
  ([18114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part010 : ℚ :=
  (569468807525 : ℚ) / 1659563168043875904

def SurrogateDiagonalTailChunk001Sub000Block039Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18114
    = surrogateDiagTailX0RatChunk001Sub000Block039Part010

theorem surrogateDiagonalTailChunk001Sub000Block039Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part010] using hcert

def TailChunk001Sub000Block039Part011SupportExplicit : Finset ℕ :=
  ([18115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part011 : ℚ :=
  (273726994875 : ℚ) / 36723101531506579456

def SurrogateDiagonalTailChunk001Sub000Block039Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18115
    = surrogateDiagTailX0RatChunk001Sub000Block039Part011

theorem surrogateDiagonalTailChunk001Sub000Block039Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part011] using hcert

def TailChunk001Sub000Block039Part012SupportExplicit : Finset ℕ :=
  ([18118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18118
    = surrogateDiagTailX0RatChunk001Sub000Block039Part012

theorem surrogateDiagonalTailChunk001Sub000Block039Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part012] using hcert

def TailChunk001Sub000Block039Part013SupportExplicit : Finset ℕ :=
  ([18119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18119
    = surrogateDiagTailX0RatChunk001Sub000Block039Part013

theorem surrogateDiagonalTailChunk001Sub000Block039Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part013] using hcert

def TailChunk001Sub000Block039Part014SupportExplicit : Finset ℕ :=
  ([18121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18121
    = surrogateDiagTailX0RatChunk001Sub000Block039Part014

theorem surrogateDiagonalTailChunk001Sub000Block039Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part014] using hcert

def TailChunk001Sub000Block039Part015SupportExplicit : Finset ℕ :=
  ([18122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part015 : ℚ :=
  (5064684317 : ℚ) / 115987309815398400

def SurrogateDiagonalTailChunk001Sub000Block039Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18122
    = surrogateDiagTailX0RatChunk001Sub000Block039Part015

theorem surrogateDiagonalTailChunk001Sub000Block039Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part015] using hcert

def TailChunk001Sub000Block039Part016SupportExplicit : Finset ℕ :=
  ([18123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part016 : ℚ :=
  (2186418804025 : ℚ) / 28627334088875624448

def SurrogateDiagonalTailChunk001Sub000Block039Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18123
    = surrogateDiagTailX0RatChunk001Sub000Block039Part016

theorem surrogateDiagonalTailChunk001Sub000Block039Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part016] using hcert

def TailChunk001Sub000Block039Part017SupportExplicit : Finset ℕ :=
  ([18127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18127
    = surrogateDiagTailX0RatChunk001Sub000Block039Part017

theorem surrogateDiagonalTailChunk001Sub000Block039Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part017] using hcert

def TailChunk001Sub000Block039Part018SupportExplicit : Finset ℕ :=
  ([18129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part018 : ℚ :=
  (1141117643225 : ℚ) / 26658746787694814784

def SurrogateDiagonalTailChunk001Sub000Block039Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18129
    = surrogateDiagTailX0RatChunk001Sub000Block039Part018

theorem surrogateDiagonalTailChunk001Sub000Block039Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part018] using hcert

def TailChunk001Sub000Block039Part019SupportExplicit : Finset ℕ :=
  ([18131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18131
    = surrogateDiagTailX0RatChunk001Sub000Block039Part019

theorem surrogateDiagonalTailChunk001Sub000Block039Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part019] using hcert

def TailChunk001Sub000Block039Part020SupportExplicit : Finset ℕ :=
  ([18133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18133
    = surrogateDiagTailX0RatChunk001Sub000Block039Part020

theorem surrogateDiagonalTailChunk001Sub000Block039Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part020] using hcert

def TailChunk001Sub000Block039Part021SupportExplicit : Finset ℕ :=
  ([18134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block039Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18134
    = surrogateDiagTailX0RatChunk001Sub000Block039Part021

theorem surrogateDiagonalTailChunk001Sub000Block039Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part021] using hcert

def TailChunk001Sub000Block039Part022SupportExplicit : Finset ℕ :=
  ([18137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part022 : ℚ :=
  (16804392287 : ℚ) / 2916492825456705600

def SurrogateDiagonalTailChunk001Sub000Block039Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18137
    = surrogateDiagTailX0RatChunk001Sub000Block039Part022

theorem surrogateDiagonalTailChunk001Sub000Block039Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part022] using hcert

def TailChunk001Sub000Block039Part023SupportExplicit : Finset ℕ :=
  ([18138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part023 : ℚ :=
  (570978505325 : ℚ) / 1668378889261161024

def SurrogateDiagonalTailChunk001Sub000Block039Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18138
    = surrogateDiagTailX0RatChunk001Sub000Block039Part023

theorem surrogateDiagonalTailChunk001Sub000Block039Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part023] using hcert

def TailChunk001Sub000Block039Part024SupportExplicit : Finset ℕ :=
  ([18139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block039Part024 : ℚ :=
  (32234260243 : ℚ) / 5567390871139123200

def SurrogateDiagonalTailChunk001Sub000Block039Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 18139
    = surrogateDiagTailX0RatChunk001Sub000Block039Part024

theorem surrogateDiagonalTailChunk001Sub000Block039Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block039Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block039Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block039Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block039Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block039Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block039HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block039Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block039Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block039Part000
    + surrogateDiagTailX0RatChunk001Sub000Block039Part001
    + surrogateDiagTailX0RatChunk001Sub000Block039Part002
    + surrogateDiagTailX0RatChunk001Sub000Block039Part003
    + surrogateDiagTailX0RatChunk001Sub000Block039Part004
    + surrogateDiagTailX0RatChunk001Sub000Block039Part005
    + surrogateDiagTailX0RatChunk001Sub000Block039Part006
    + surrogateDiagTailX0RatChunk001Sub000Block039Part007
    + surrogateDiagTailX0RatChunk001Sub000Block039Part008
    + surrogateDiagTailX0RatChunk001Sub000Block039Part009

def surrogateDiagonalTailChunk001Sub000Block039MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block039Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block039Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block039Part010
    + surrogateDiagTailX0RatChunk001Sub000Block039Part011
    + surrogateDiagTailX0RatChunk001Sub000Block039Part012
    + surrogateDiagTailX0RatChunk001Sub000Block039Part013
    + surrogateDiagTailX0RatChunk001Sub000Block039Part014
    + surrogateDiagTailX0RatChunk001Sub000Block039Part015
    + surrogateDiagTailX0RatChunk001Sub000Block039Part016
    + surrogateDiagTailX0RatChunk001Sub000Block039Part017
    + surrogateDiagTailX0RatChunk001Sub000Block039Part018
    + surrogateDiagTailX0RatChunk001Sub000Block039Part019

def surrogateDiagonalTailChunk001Sub000Block039TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block039Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block039Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block039Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block039Part020
    + surrogateDiagTailX0RatChunk001Sub000Block039Part021
    + surrogateDiagTailX0RatChunk001Sub000Block039Part022
    + surrogateDiagTailX0RatChunk001Sub000Block039Part023
    + surrogateDiagTailX0RatChunk001Sub000Block039Part024

def surrogateDiagonalTailChunk001Sub000Block039Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block039HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block039MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block039TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block039 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block039Part000
    + surrogateDiagTailX0RatChunk001Sub000Block039Part001
    + surrogateDiagTailX0RatChunk001Sub000Block039Part002
    + surrogateDiagTailX0RatChunk001Sub000Block039Part003
    + surrogateDiagTailX0RatChunk001Sub000Block039Part004
    + surrogateDiagTailX0RatChunk001Sub000Block039Part005
    + surrogateDiagTailX0RatChunk001Sub000Block039Part006
    + surrogateDiagTailX0RatChunk001Sub000Block039Part007
    + surrogateDiagTailX0RatChunk001Sub000Block039Part008
    + surrogateDiagTailX0RatChunk001Sub000Block039Part009
    + surrogateDiagTailX0RatChunk001Sub000Block039Part010
    + surrogateDiagTailX0RatChunk001Sub000Block039Part011
    + surrogateDiagTailX0RatChunk001Sub000Block039Part012
    + surrogateDiagTailX0RatChunk001Sub000Block039Part013
    + surrogateDiagTailX0RatChunk001Sub000Block039Part014
    + surrogateDiagTailX0RatChunk001Sub000Block039Part015
    + surrogateDiagTailX0RatChunk001Sub000Block039Part016
    + surrogateDiagTailX0RatChunk001Sub000Block039Part017
    + surrogateDiagTailX0RatChunk001Sub000Block039Part018
    + surrogateDiagTailX0RatChunk001Sub000Block039Part019
    + surrogateDiagTailX0RatChunk001Sub000Block039Part020
    + surrogateDiagTailX0RatChunk001Sub000Block039Part021
    + surrogateDiagTailX0RatChunk001Sub000Block039Part022
    + surrogateDiagTailX0RatChunk001Sub000Block039Part023
    + surrogateDiagTailX0RatChunk001Sub000Block039Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block039_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block039Head + surrogateDiagTailX0RatChunk001Sub000Block039Mid + surrogateDiagTailX0RatChunk001Sub000Block039Tail =
      surrogateDiagTailX0RatChunk001Sub000Block039 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block039Head surrogateDiagTailX0RatChunk001Sub000Block039Mid surrogateDiagTailX0RatChunk001Sub000Block039Tail surrogateDiagTailX0RatChunk001Sub000Block039
  ring

def SurrogateDiagonalTailChunk001Sub000Block039HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block039HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block039Head

def SurrogateDiagonalTailChunk001Sub000Block039MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block039MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block039Mid

def SurrogateDiagonalTailChunk001Sub000Block039TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block039TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block039Tail

theorem surrogateDiagonalTailChunk001Sub000Block039_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block039HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block039MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block039TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block039Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block039 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block039HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block039MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block039TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block039Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block039_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
