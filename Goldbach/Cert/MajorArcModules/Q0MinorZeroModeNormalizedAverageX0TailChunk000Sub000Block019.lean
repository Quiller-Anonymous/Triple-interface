import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [19,20). -/

/- Block 019 covers tail-support indices [475,500) and q from 829 to 874. -/

def TailChunk000Sub000Block019Part000SupportExplicit : Finset ℕ :=
  ([829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part000 : ℚ :=
  (3178489625 : ℚ) / 14509858831488

def SurrogateDiagonalTailChunk000Sub000Block019Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 829
    = surrogateDiagTailX0RatChunk000Sub000Block019Part000

theorem surrogateDiagonalTailChunk000Sub000Block019Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part000] using hcert

def TailChunk000Sub000Block019Part001SupportExplicit : Finset ℕ :=
  ([830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part001 : ℚ :=
  (12764552375 : ℚ) / 3617697474816

def SurrogateDiagonalTailChunk000Sub000Block019Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 830
    = surrogateDiagTailX0RatChunk000Sub000Block019Part001

theorem surrogateDiagonalTailChunk000Sub000Block019Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part001] using hcert

def TailChunk000Sub000Block019Part002SupportExplicit : Finset ℕ :=
  ([831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part002 : ℚ :=
  (11467925 : ℚ) / 15474087936

def SurrogateDiagonalTailChunk000Sub000Block019Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 831
    = surrogateDiagTailX0RatChunk000Sub000Block019Part002

theorem surrogateDiagonalTailChunk000Sub000Block019Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part002] using hcert

def TailChunk000Sub000Block019Part003SupportExplicit : Finset ℕ :=
  ([834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part003 : ℚ :=
  (5754575 : ℚ) / 967130496

def SurrogateDiagonalTailChunk000Sub000Block019Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 834
    = surrogateDiagTailX0RatChunk000Sub000Block019Part003

theorem surrogateDiagonalTailChunk000Sub000Block019Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part003] using hcert

def TailChunk000Sub000Block019Part004SupportExplicit : Finset ℕ :=
  ([835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part004 : ℚ :=
  (103116109325 : ℚ) / 243035200840704

def SurrogateDiagonalTailChunk000Sub000Block019Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 835
    = surrogateDiagTailX0RatChunk000Sub000Block019Part004

theorem surrogateDiagonalTailChunk000Sub000Block019Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part004] using hcert

def TailChunk000Sub000Block019Part005SupportExplicit : Finset ℕ :=
  ([838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part005 : ℚ :=
  (21896845725 : ℚ) / 12722742446348

def SurrogateDiagonalTailChunk000Sub000Block019Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 838
    = surrogateDiagTailX0RatChunk000Sub000Block019Part005

theorem surrogateDiagonalTailChunk000Sub000Block019Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part005] using hcert

def TailChunk000Sub000Block019Part006SupportExplicit : Finset ℕ :=
  ([839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part006 : ℚ :=
  (87902134875 : ℚ) / 411037720719256

def SurrogateDiagonalTailChunk000Sub000Block019Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 839
    = surrogateDiagTailX0RatChunk000Sub000Block019Part006

theorem surrogateDiagonalTailChunk000Sub000Block019Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part006] using hcert

def TailChunk000Sub000Block019Part007SupportExplicit : Finset ℕ :=
  ([842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part007 : ℚ :=
  (294751783 : ℚ) / 172906574400

def SurrogateDiagonalTailChunk000Sub000Block019Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 842
    = surrogateDiagTailX0RatChunk000Sub000Block019Part007

theorem surrogateDiagonalTailChunk000Sub000Block019Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part007] using hcert

def TailChunk000Sub000Block019Part008SupportExplicit : Finset ℕ :=
  ([843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part008 : ℚ :=
  (1416183 : ℚ) / 1966899200

def SurrogateDiagonalTailChunk000Sub000Block019Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 843
    = surrogateDiagTailX0RatChunk000Sub000Block019Part008

theorem surrogateDiagonalTailChunk000Sub000Block019Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part008] using hcert

def TailChunk000Sub000Block019Part009SupportExplicit : Finset ℕ :=
  ([849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part009 : ℚ :=
  (11970125 : ℚ) / 16864177536

def SurrogateDiagonalTailChunk000Sub000Block019Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 849
    = surrogateDiagTailX0RatChunk000Sub000Block019Part009

theorem surrogateDiagonalTailChunk000Sub000Block019Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part009] using hcert

def TailChunk000Sub000Block019Part010SupportExplicit : Finset ℕ :=
  ([851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part010 : ℚ :=
  (252396973825 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block019Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 851
    = surrogateDiagTailX0RatChunk000Sub000Block019Part010

theorem surrogateDiagonalTailChunk000Sub000Block019Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part010] using hcert

def TailChunk000Sub000Block019Part011SupportExplicit : Finset ℕ :=
  ([853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part011 : ℚ :=
  (3365191625 : ℚ) / 16266728535168

def SurrogateDiagonalTailChunk000Sub000Block019Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 853
    = surrogateDiagTailX0RatChunk000Sub000Block019Part011

theorem surrogateDiagonalTailChunk000Sub000Block019Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part011] using hcert

def TailChunk000Sub000Block019Part012SupportExplicit : Finset ℕ :=
  ([854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part012 : ℚ :=
  (574079129 : ℚ) / 209993990400

def SurrogateDiagonalTailChunk000Sub000Block019Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 854
    = surrogateDiagTailX0RatChunk000Sub000Block019Part012

theorem surrogateDiagonalTailChunk000Sub000Block019Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part012] using hcert

def TailChunk000Sub000Block019Part013SupportExplicit : Finset ℕ :=
  ([857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part013 : ℚ :=
  (91714318875 : ℚ) / 447507855087616

def SurrogateDiagonalTailChunk000Sub000Block019Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 857
    = surrogateDiagTailX0RatChunk000Sub000Block019Part013

theorem surrogateDiagonalTailChunk000Sub000Block019Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part013] using hcert

def TailChunk000Sub000Block019Part014SupportExplicit : Finset ℕ :=
  ([858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part014 : ℚ :=
  (75971491 : ℚ) / 8296058880

def SurrogateDiagonalTailChunk000Sub000Block019Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 858
    = surrogateDiagTailX0RatChunk000Sub000Block019Part014

theorem surrogateDiagonalTailChunk000Sub000Block019Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part014] using hcert

def TailChunk000Sub000Block019Part015SupportExplicit : Finset ℕ :=
  ([859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part015 : ℚ :=
  (115201671125 : ℚ) / 677557277978724

def SurrogateDiagonalTailChunk000Sub000Block019Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 859
    = surrogateDiagTailX0RatChunk000Sub000Block019Part015

theorem surrogateDiagonalTailChunk000Sub000Block019Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part015] using hcert

def TailChunk000Sub000Block019Part016SupportExplicit : Finset ℕ :=
  ([861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part016 : ℚ :=
  (668380253 : ℚ) / 589941964800

def SurrogateDiagonalTailChunk000Sub000Block019Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 861
    = surrogateDiagTailX0RatChunk000Sub000Block019Part016

theorem surrogateDiagonalTailChunk000Sub000Block019Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part016] using hcert

def TailChunk000Sub000Block019Part017SupportExplicit : Finset ℕ :=
  ([862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part017 : ℚ :=
  (1019642129 : ℚ) / 683896952040

def SurrogateDiagonalTailChunk000Sub000Block019Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 862
    = surrogateDiagTailX0RatChunk000Sub000Block019Part017

theorem surrogateDiagonalTailChunk000Sub000Block019Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part017] using hcert

def TailChunk000Sub000Block019Part018SupportExplicit : Finset ℕ :=
  ([863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part018 : ℚ :=
  (93003028875 : ℚ) / 460187340677656

def SurrogateDiagonalTailChunk000Sub000Block019Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 863
    = surrogateDiagTailX0RatChunk000Sub000Block019Part018

theorem surrogateDiagonalTailChunk000Sub000Block019Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part018] using hcert

def TailChunk000Sub000Block019Part019SupportExplicit : Finset ℕ :=
  ([865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part019 : ℚ :=
  (16131096075 : ℚ) / 46687365259264

def SurrogateDiagonalTailChunk000Sub000Block019Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 865
    = surrogateDiagTailX0RatChunk000Sub000Block019Part019

theorem surrogateDiagonalTailChunk000Sub000Block019Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part019] using hcert

def TailChunk000Sub000Block019Part020SupportExplicit : Finset ℕ :=
  ([866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part020 : ℚ :=
  (7794855175 : ℚ) / 4838261538816

def SurrogateDiagonalTailChunk000Sub000Block019Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 866
    = surrogateDiagTailX0RatChunk000Sub000Block019Part020

theorem surrogateDiagonalTailChunk000Sub000Block019Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part020] using hcert

def TailChunk000Sub000Block019Part021SupportExplicit : Finset ℕ :=
  ([869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part021 : ℚ :=
  (2529609661 : ℚ) / 9255614752800

def SurrogateDiagonalTailChunk000Sub000Block019Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 869
    = surrogateDiagTailX0RatChunk000Sub000Block019Part021

theorem surrogateDiagonalTailChunk000Sub000Block019Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part021] using hcert

def TailChunk000Sub000Block019Part022SupportExplicit : Finset ℕ :=
  ([870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part022 : ℚ :=
  (68481428125 : ℚ) / 6295336255488

def SurrogateDiagonalTailChunk000Sub000Block019Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 870
    = surrogateDiagTailX0RatChunk000Sub000Block019Part022

theorem surrogateDiagonalTailChunk000Sub000Block019Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part022] using hcert

def TailChunk000Sub000Block019Part023SupportExplicit : Finset ℕ :=
  ([871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part023 : ℚ :=
  (218819702875 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block019Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 871
    = surrogateDiagTailX0RatChunk000Sub000Block019Part023

theorem surrogateDiagonalTailChunk000Sub000Block019Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part023] using hcert

def TailChunk000Sub000Block019Part024SupportExplicit : Finset ℕ :=
  ([874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block019Part024 : ℚ :=
  (19908705125 : ℚ) / 10248406711488

def SurrogateDiagonalTailChunk000Sub000Block019Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 874
    = surrogateDiagTailX0RatChunk000Sub000Block019Part024

theorem surrogateDiagonalTailChunk000Sub000Block019Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block019Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block019Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block019Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block019Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block019Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block019HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block019Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block019Part000
    + surrogateDiagTailX0RatChunk000Sub000Block019Part001
    + surrogateDiagTailX0RatChunk000Sub000Block019Part002
    + surrogateDiagTailX0RatChunk000Sub000Block019Part003
    + surrogateDiagTailX0RatChunk000Sub000Block019Part004
    + surrogateDiagTailX0RatChunk000Sub000Block019Part005
    + surrogateDiagTailX0RatChunk000Sub000Block019Part006
    + surrogateDiagTailX0RatChunk000Sub000Block019Part007
    + surrogateDiagTailX0RatChunk000Sub000Block019Part008
    + surrogateDiagTailX0RatChunk000Sub000Block019Part009

def surrogateDiagonalTailChunk000Sub000Block019MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block019Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block019Part010
    + surrogateDiagTailX0RatChunk000Sub000Block019Part011
    + surrogateDiagTailX0RatChunk000Sub000Block019Part012
    + surrogateDiagTailX0RatChunk000Sub000Block019Part013
    + surrogateDiagTailX0RatChunk000Sub000Block019Part014
    + surrogateDiagTailX0RatChunk000Sub000Block019Part015
    + surrogateDiagTailX0RatChunk000Sub000Block019Part016
    + surrogateDiagTailX0RatChunk000Sub000Block019Part017
    + surrogateDiagTailX0RatChunk000Sub000Block019Part018
    + surrogateDiagTailX0RatChunk000Sub000Block019Part019

def surrogateDiagonalTailChunk000Sub000Block019TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block019Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block019Part020
    + surrogateDiagTailX0RatChunk000Sub000Block019Part021
    + surrogateDiagTailX0RatChunk000Sub000Block019Part022
    + surrogateDiagTailX0RatChunk000Sub000Block019Part023
    + surrogateDiagTailX0RatChunk000Sub000Block019Part024

def surrogateDiagonalTailChunk000Sub000Block019Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block019HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block019MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block019TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block019 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block019Part000
    + surrogateDiagTailX0RatChunk000Sub000Block019Part001
    + surrogateDiagTailX0RatChunk000Sub000Block019Part002
    + surrogateDiagTailX0RatChunk000Sub000Block019Part003
    + surrogateDiagTailX0RatChunk000Sub000Block019Part004
    + surrogateDiagTailX0RatChunk000Sub000Block019Part005
    + surrogateDiagTailX0RatChunk000Sub000Block019Part006
    + surrogateDiagTailX0RatChunk000Sub000Block019Part007
    + surrogateDiagTailX0RatChunk000Sub000Block019Part008
    + surrogateDiagTailX0RatChunk000Sub000Block019Part009
    + surrogateDiagTailX0RatChunk000Sub000Block019Part010
    + surrogateDiagTailX0RatChunk000Sub000Block019Part011
    + surrogateDiagTailX0RatChunk000Sub000Block019Part012
    + surrogateDiagTailX0RatChunk000Sub000Block019Part013
    + surrogateDiagTailX0RatChunk000Sub000Block019Part014
    + surrogateDiagTailX0RatChunk000Sub000Block019Part015
    + surrogateDiagTailX0RatChunk000Sub000Block019Part016
    + surrogateDiagTailX0RatChunk000Sub000Block019Part017
    + surrogateDiagTailX0RatChunk000Sub000Block019Part018
    + surrogateDiagTailX0RatChunk000Sub000Block019Part019
    + surrogateDiagTailX0RatChunk000Sub000Block019Part020
    + surrogateDiagTailX0RatChunk000Sub000Block019Part021
    + surrogateDiagTailX0RatChunk000Sub000Block019Part022
    + surrogateDiagTailX0RatChunk000Sub000Block019Part023
    + surrogateDiagTailX0RatChunk000Sub000Block019Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block019_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block019Head + surrogateDiagTailX0RatChunk000Sub000Block019Mid + surrogateDiagTailX0RatChunk000Sub000Block019Tail =
      surrogateDiagTailX0RatChunk000Sub000Block019 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block019Head surrogateDiagTailX0RatChunk000Sub000Block019Mid surrogateDiagTailX0RatChunk000Sub000Block019Tail surrogateDiagTailX0RatChunk000Sub000Block019
  ring

def SurrogateDiagonalTailChunk000Sub000Block019HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block019HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block019Head

def SurrogateDiagonalTailChunk000Sub000Block019MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block019MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block019Mid

def SurrogateDiagonalTailChunk000Sub000Block019TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block019TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block019Tail

theorem surrogateDiagonalTailChunk000Sub000Block019_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block019HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block019MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block019TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block019Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block019 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block019HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block019MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block019TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block019Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block019_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
