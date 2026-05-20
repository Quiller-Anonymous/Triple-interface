import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [17,18). -/

/- Block 017 covers tail-support indices [425,450) and q from 751 to 789. -/

def TailChunk000Sub000Block017Part000SupportExplicit : Finset ℕ :=
  ([751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part000 : ℚ :=
  (9858173479 : ℚ) / 31646953125000

def SurrogateDiagonalTailChunk000Sub000Block017Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 751
    = surrogateDiagTailX0RatChunk000Sub000Block017Part000

theorem surrogateDiagonalTailChunk000Sub000Block017Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part000] using hcert

def TailChunk000Sub000Block017Part001SupportExplicit : Finset ℕ :=
  ([753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part001 : ℚ :=
  (725911529 : ℚ) / 781406250000

def SurrogateDiagonalTailChunk000Sub000Block017Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 753
    = surrogateDiagTailX0RatChunk000Sub000Block017Part001

theorem surrogateDiagonalTailChunk000Sub000Block017Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part001] using hcert

def TailChunk000Sub000Block017Part002SupportExplicit : Finset ℕ :=
  ([754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part002 : ℚ :=
  (25791522025 : ℚ) / 7967534948352

def SurrogateDiagonalTailChunk000Sub000Block017Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 754
    = surrogateDiagTailX0RatChunk000Sub000Block017Part002

theorem surrogateDiagonalTailChunk000Sub000Block017Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part002] using hcert

def TailChunk000Sub000Block017Part003SupportExplicit : Finset ℕ :=
  ([755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part003 : ℚ :=
  (1742442943 : ℚ) / 3240648000000

def SurrogateDiagonalTailChunk000Sub000Block017Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 755
    = surrogateDiagTailX0RatChunk000Sub000Block017Part003

theorem surrogateDiagonalTailChunk000Sub000Block017Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part003] using hcert

def TailChunk000Sub000Block017Part004SupportExplicit : Finset ℕ :=
  ([757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part004 : ℚ :=
  (35772583825 : ℚ) / 116685260705664

def SurrogateDiagonalTailChunk000Sub000Block017Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 757
    = surrogateDiagTailX0RatChunk000Sub000Block017Part004

theorem surrogateDiagonalTailChunk000Sub000Block017Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part004] using hcert

def TailChunk000Sub000Block017Part005SupportExplicit : Finset ℕ :=
  ([758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part005 : ℚ :=
  (58214106275 : ℚ) / 25524900779364

def SurrogateDiagonalTailChunk000Sub000Block017Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 758
    = surrogateDiagTailX0RatChunk000Sub000Block017Part005

theorem surrogateDiagonalTailChunk000Sub000Block017Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part005] using hcert

def TailChunk000Sub000Block017Part006SupportExplicit : Finset ℕ :=
  ([759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part006 : ℚ :=
  (5675667301 : ℚ) / 3748845619200

def SurrogateDiagonalTailChunk000Sub000Block017Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 759
    = surrogateDiagTailX0RatChunk000Sub000Block017Part006

theorem surrogateDiagonalTailChunk000Sub000Block017Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part006] using hcert

def TailChunk000Sub000Block017Part007SupportExplicit : Finset ℕ :=
  ([761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part007 : ℚ :=
  (578541879 : ℚ) / 2224589895680

def SurrogateDiagonalTailChunk000Sub000Block017Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 761
    = surrogateDiagTailX0RatChunk000Sub000Block017Part007

theorem surrogateDiagonalTailChunk000Sub000Block017Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part007] using hcert

def TailChunk000Sub000Block017Part008SupportExplicit : Finset ℕ :=
  ([762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part008 : ℚ :=
  (2600525 : ℚ) / 336063168

def SurrogateDiagonalTailChunk000Sub000Block017Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 762
    = surrogateDiagTailX0RatChunk000Sub000Block017Part008

theorem surrogateDiagonalTailChunk000Sub000Block017Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part008] using hcert

def TailChunk000Sub000Block017Part009SupportExplicit : Finset ℕ :=
  ([763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part009 : ℚ :=
  (188517790375 : ℚ) / 440886582724608

def SurrogateDiagonalTailChunk000Sub000Block017Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 763
    = surrogateDiagTailX0RatChunk000Sub000Block017Part009

theorem surrogateDiagonalTailChunk000Sub000Block017Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part009] using hcert

def TailChunk000Sub000Block017Part010SupportExplicit : Finset ℕ :=
  ([766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part010 : ℚ :=
  (59449384475 : ℚ) / 26622590673444

def SurrogateDiagonalTailChunk000Sub000Block017Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 766
    = surrogateDiagTailX0RatChunk000Sub000Block017Part010

theorem surrogateDiagonalTailChunk000Sub000Block017Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part010] using hcert

def TailChunk000Sub000Block017Part011SupportExplicit : Finset ℕ :=
  ([767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part011 : ℚ :=
  (232061997175 : ℚ) / 586764482070528

def SurrogateDiagonalTailChunk000Sub000Block017Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 767
    = surrogateDiagTailX0RatChunk000Sub000Block017Part011

theorem surrogateDiagonalTailChunk000Sub000Block017Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part011] using hcert

def TailChunk000Sub000Block017Part012SupportExplicit : Finset ℕ :=
  ([769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part012 : ℚ :=
  (2735044625 : ℚ) / 10739565723648

def SurrogateDiagonalTailChunk000Sub000Block017Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 769
    = surrogateDiagTailX0RatChunk000Sub000Block017Part012

theorem surrogateDiagonalTailChunk000Sub000Block017Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part012] using hcert

def TailChunk000Sub000Block017Part013SupportExplicit : Finset ℕ :=
  ([770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part013 : ℚ :=
  (83430641 : ℚ) / 9217843200

def SurrogateDiagonalTailChunk000Sub000Block017Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 770
    = surrogateDiagTailX0RatChunk000Sub000Block017Part013

theorem surrogateDiagonalTailChunk000Sub000Block017Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part013] using hcert

def TailChunk000Sub000Block017Part014SupportExplicit : Finset ℕ :=
  ([771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part014 : ℚ :=
  (76102210925 : ℚ) / 85916525789184

def SurrogateDiagonalTailChunk000Sub000Block017Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 771
    = surrogateDiagTailX0RatChunk000Sub000Block017Part014

theorem surrogateDiagonalTailChunk000Sub000Block017Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part014] using hcert

def TailChunk000Sub000Block017Part015SupportExplicit : Finset ℕ :=
  ([773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part015 : ℚ :=
  (261105234775 : ℚ) / 888169919104128

def SurrogateDiagonalTailChunk000Sub000Block017Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 773
    = surrogateDiagTailX0RatChunk000Sub000Block017Part015

theorem surrogateDiagonalTailChunk000Sub000Block017Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part015] using hcert

def TailChunk000Sub000Block017Part016SupportExplicit : Finset ℕ :=
  ([777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part016 : ℚ :=
  (2038145425 : ℚ) / 1360761057792

def SurrogateDiagonalTailChunk000Sub000Block017Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 777
    = surrogateDiagTailX0RatChunk000Sub000Block017Part016

theorem surrogateDiagonalTailChunk000Sub000Block017Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part016] using hcert

def TailChunk000Sub000Block017Part017SupportExplicit : Finset ℕ :=
  ([778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part017 : ℚ :=
  (61326618275 : ℚ) / 28335035793984

def SurrogateDiagonalTailChunk000Sub000Block017Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 778
    = surrogateDiagTailX0RatChunk000Sub000Block017Part017

theorem surrogateDiagonalTailChunk000Sub000Block017Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part017] using hcert

def TailChunk000Sub000Block017Part018SupportExplicit : Finset ℕ :=
  ([779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part018 : ℚ :=
  (9752764171 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block017Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 779
    = surrogateDiagTailX0RatChunk000Sub000Block017Part018

theorem surrogateDiagonalTailChunk000Sub000Block017Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part018] using hcert

def TailChunk000Sub000Block017Part019SupportExplicit : Finset ℕ :=
  ([781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part019 : ℚ :=
  (2753021673 : ℚ) / 8004934000000

def SurrogateDiagonalTailChunk000Sub000Block017Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 781
    = surrogateDiagTailX0RatChunk000Sub000Block017Part019

theorem surrogateDiagonalTailChunk000Sub000Block017Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part019] using hcert

def TailChunk000Sub000Block017Part020SupportExplicit : Finset ℕ :=
  ([782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part020 : ℚ :=
  (111642648775 : ℚ) / 38388179140608

def SurrogateDiagonalTailChunk000Sub000Block017Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 782
    = surrogateDiagTailX0RatChunk000Sub000Block017Part020

theorem surrogateDiagonalTailChunk000Sub000Block017Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part020] using hcert

def TailChunk000Sub000Block017Part021SupportExplicit : Finset ℕ :=
  ([785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part021 : ℚ :=
  (209658635275 : ℚ) / 379109980274688

def SurrogateDiagonalTailChunk000Sub000Block017Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 785
    = surrogateDiagTailX0RatChunk000Sub000Block017Part021

theorem surrogateDiagonalTailChunk000Sub000Block017Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part021] using hcert

def TailChunk000Sub000Block017Part022SupportExplicit : Finset ℕ :=
  ([786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part022 : ℚ :=
  (1575957971 : ℚ) / 228533697600

def SurrogateDiagonalTailChunk000Sub000Block017Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 786
    = surrogateDiagTailX0RatChunk000Sub000Block017Part022

theorem surrogateDiagonalTailChunk000Sub000Block017Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part022] using hcert

def TailChunk000Sub000Block017Part023SupportExplicit : Finset ℕ :=
  ([787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part023 : ℚ :=
  (2864581625 : ℚ) / 11782352839368

def SurrogateDiagonalTailChunk000Sub000Block017Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 787
    = surrogateDiagTailX0RatChunk000Sub000Block017Part023

theorem surrogateDiagonalTailChunk000Sub000Block017Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part023] using hcert

def TailChunk000Sub000Block017Part024SupportExplicit : Finset ℕ :=
  ([789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block017Part024 : ℚ :=
  (172263613075 : ℚ) / 188517645429888

def SurrogateDiagonalTailChunk000Sub000Block017Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 789
    = surrogateDiagTailX0RatChunk000Sub000Block017Part024

theorem surrogateDiagonalTailChunk000Sub000Block017Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block017Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block017Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block017Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block017Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block017Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block017HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block017Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block017Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block017Part000
    + surrogateDiagTailX0RatChunk000Sub000Block017Part001
    + surrogateDiagTailX0RatChunk000Sub000Block017Part002
    + surrogateDiagTailX0RatChunk000Sub000Block017Part003
    + surrogateDiagTailX0RatChunk000Sub000Block017Part004
    + surrogateDiagTailX0RatChunk000Sub000Block017Part005
    + surrogateDiagTailX0RatChunk000Sub000Block017Part006
    + surrogateDiagTailX0RatChunk000Sub000Block017Part007
    + surrogateDiagTailX0RatChunk000Sub000Block017Part008
    + surrogateDiagTailX0RatChunk000Sub000Block017Part009

def surrogateDiagonalTailChunk000Sub000Block017MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block017Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block017Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block017Part010
    + surrogateDiagTailX0RatChunk000Sub000Block017Part011
    + surrogateDiagTailX0RatChunk000Sub000Block017Part012
    + surrogateDiagTailX0RatChunk000Sub000Block017Part013
    + surrogateDiagTailX0RatChunk000Sub000Block017Part014
    + surrogateDiagTailX0RatChunk000Sub000Block017Part015
    + surrogateDiagTailX0RatChunk000Sub000Block017Part016
    + surrogateDiagTailX0RatChunk000Sub000Block017Part017
    + surrogateDiagTailX0RatChunk000Sub000Block017Part018
    + surrogateDiagTailX0RatChunk000Sub000Block017Part019

def surrogateDiagonalTailChunk000Sub000Block017TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block017Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block017Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block017Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block017Part020
    + surrogateDiagTailX0RatChunk000Sub000Block017Part021
    + surrogateDiagTailX0RatChunk000Sub000Block017Part022
    + surrogateDiagTailX0RatChunk000Sub000Block017Part023
    + surrogateDiagTailX0RatChunk000Sub000Block017Part024

def surrogateDiagonalTailChunk000Sub000Block017Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block017HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block017MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block017TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block017 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block017Part000
    + surrogateDiagTailX0RatChunk000Sub000Block017Part001
    + surrogateDiagTailX0RatChunk000Sub000Block017Part002
    + surrogateDiagTailX0RatChunk000Sub000Block017Part003
    + surrogateDiagTailX0RatChunk000Sub000Block017Part004
    + surrogateDiagTailX0RatChunk000Sub000Block017Part005
    + surrogateDiagTailX0RatChunk000Sub000Block017Part006
    + surrogateDiagTailX0RatChunk000Sub000Block017Part007
    + surrogateDiagTailX0RatChunk000Sub000Block017Part008
    + surrogateDiagTailX0RatChunk000Sub000Block017Part009
    + surrogateDiagTailX0RatChunk000Sub000Block017Part010
    + surrogateDiagTailX0RatChunk000Sub000Block017Part011
    + surrogateDiagTailX0RatChunk000Sub000Block017Part012
    + surrogateDiagTailX0RatChunk000Sub000Block017Part013
    + surrogateDiagTailX0RatChunk000Sub000Block017Part014
    + surrogateDiagTailX0RatChunk000Sub000Block017Part015
    + surrogateDiagTailX0RatChunk000Sub000Block017Part016
    + surrogateDiagTailX0RatChunk000Sub000Block017Part017
    + surrogateDiagTailX0RatChunk000Sub000Block017Part018
    + surrogateDiagTailX0RatChunk000Sub000Block017Part019
    + surrogateDiagTailX0RatChunk000Sub000Block017Part020
    + surrogateDiagTailX0RatChunk000Sub000Block017Part021
    + surrogateDiagTailX0RatChunk000Sub000Block017Part022
    + surrogateDiagTailX0RatChunk000Sub000Block017Part023
    + surrogateDiagTailX0RatChunk000Sub000Block017Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block017_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block017Head + surrogateDiagTailX0RatChunk000Sub000Block017Mid + surrogateDiagTailX0RatChunk000Sub000Block017Tail =
      surrogateDiagTailX0RatChunk000Sub000Block017 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block017Head surrogateDiagTailX0RatChunk000Sub000Block017Mid surrogateDiagTailX0RatChunk000Sub000Block017Tail surrogateDiagTailX0RatChunk000Sub000Block017
  ring

def SurrogateDiagonalTailChunk000Sub000Block017HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block017HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block017Head

def SurrogateDiagonalTailChunk000Sub000Block017MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block017MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block017Mid

def SurrogateDiagonalTailChunk000Sub000Block017TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block017TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block017Tail

theorem surrogateDiagonalTailChunk000Sub000Block017_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block017HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block017MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block017TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block017Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block017 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block017HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block017MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block017TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block017Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block017_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
