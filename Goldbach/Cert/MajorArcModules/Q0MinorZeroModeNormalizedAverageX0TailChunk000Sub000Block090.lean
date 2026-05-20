import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [90,91). -/

/- Block 090 covers tail-support indices [2250,2275) and q from 3754 to 3794. -/

def TailChunk000Sub000Block090Part000SupportExplicit : Finset ℕ :=
  ([3754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part000 : ℚ :=
  (4491989475 : ℚ) / 210688514130304

def SurrogateDiagonalTailChunk000Sub000Block090Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3754
    = surrogateDiagTailX0RatChunk000Sub000Block090Part000

theorem surrogateDiagonalTailChunk000Sub000Block090Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part000] using hcert

def TailChunk000Sub000Block090Part001SupportExplicit : Finset ℕ :=
  ([3755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part001 : ℚ :=
  (10330849493 : ℚ) / 2700540000000000

def SurrogateDiagonalTailChunk000Sub000Block090Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3755
    = surrogateDiagTailX0RatChunk000Sub000Block090Part001

theorem surrogateDiagonalTailChunk000Sub000Block090Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part001] using hcert

def TailChunk000Sub000Block090Part002SupportExplicit : Finset ℕ :=
  ([3758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part002 : ℚ :=
  (441241858975 : ℚ) / 31103496329014728

def SurrogateDiagonalTailChunk000Sub000Block090Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3758
    = surrogateDiagTailX0RatChunk000Sub000Block090Part002

theorem surrogateDiagonalTailChunk000Sub000Block090Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part002] using hcert

def TailChunk000Sub000Block090Part003SupportExplicit : Finset ℕ :=
  ([3759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part003 : ℚ :=
  (22144824725 : ℚ) / 1927827131848704

def SurrogateDiagonalTailChunk000Sub000Block090Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3759
    = surrogateDiagTailX0RatChunk000Sub000Block090Part003

theorem surrogateDiagonalTailChunk000Sub000Block090Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part003] using hcert

def TailChunk000Sub000Block090Part004SupportExplicit : Finset ℕ :=
  ([3761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part004 : ℚ :=
  (70711459879 : ℚ) / 19991170810675200

def SurrogateDiagonalTailChunk000Sub000Block090Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3761
    = surrogateDiagTailX0RatChunk000Sub000Block090Part004

theorem surrogateDiagonalTailChunk000Sub000Block090Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part004] using hcert

def TailChunk000Sub000Block090Part005SupportExplicit : Finset ℕ :=
  ([3763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part005 : ℚ :=
  (67732139113 : ℚ) / 17558701054003200

def SurrogateDiagonalTailChunk000Sub000Block090Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3763
    = surrogateDiagTailX0RatChunk000Sub000Block090Part005

theorem surrogateDiagonalTailChunk000Sub000Block090Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part005] using hcert

def TailChunk000Sub000Block090Part006SupportExplicit : Finset ℕ :=
  ([3765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part006 : ℚ :=
  (29320311937 : ℚ) / 1600320000000000

def SurrogateDiagonalTailChunk000Sub000Block090Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3765
    = surrogateDiagTailX0RatChunk000Sub000Block090Part006

theorem surrogateDiagonalTailChunk000Sub000Block090Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part006] using hcert

def TailChunk000Sub000Block090Part007SupportExplicit : Finset ℕ :=
  ([3766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part007 : ℚ :=
  (8337473575 : ℚ) / 249514755692544

def SurrogateDiagonalTailChunk000Sub000Block090Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3766
    = surrogateDiagTailX0RatChunk000Sub000Block090Part007

theorem surrogateDiagonalTailChunk000Sub000Block090Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part007] using hcert

def TailChunk000Sub000Block090Part008SupportExplicit : Finset ℕ :=
  ([3767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part008 : ℚ :=
  (1773431367775 : ℚ) / 502976994672717768

def SurrogateDiagonalTailChunk000Sub000Block090Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3767
    = surrogateDiagTailX0RatChunk000Sub000Block090Part008

theorem surrogateDiagonalTailChunk000Sub000Block090Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part008] using hcert

def TailChunk000Sub000Block090Part009SupportExplicit : Finset ℕ :=
  ([3769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part009 : ℚ :=
  (221958765625 : ℚ) / 126011576235151872

def SurrogateDiagonalTailChunk000Sub000Block090Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3769
    = surrogateDiagTailX0RatChunk000Sub000Block090Part009

theorem surrogateDiagonalTailChunk000Sub000Block090Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part009] using hcert

def TailChunk000Sub000Block090Part010SupportExplicit : Finset ℕ :=
  ([3770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part010 : ℚ :=
  (174681194675 : ℚ) / 4079377893556224

def SurrogateDiagonalTailChunk000Sub000Block090Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3770
    = surrogateDiagTailX0RatChunk000Sub000Block090Part010

theorem surrogateDiagonalTailChunk000Sub000Block090Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part010] using hcert

def TailChunk000Sub000Block090Part011SupportExplicit : Finset ℕ :=
  ([3774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part011 : ℚ :=
  (95696289925 : ℚ) / 1100973292388352

def SurrogateDiagonalTailChunk000Sub000Block090Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3774
    = surrogateDiagTailX0RatChunk000Sub000Block090Part011

theorem surrogateDiagonalTailChunk000Sub000Block090Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part011] using hcert

def TailChunk000Sub000Block090Part012SupportExplicit : Finset ℕ :=
  ([3777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part012 : ℚ :=
  (693115223275 : ℚ) / 100200388634352768

def SurrogateDiagonalTailChunk000Sub000Block090Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3777
    = surrogateDiagTailX0RatChunk000Sub000Block090Part012

theorem surrogateDiagonalTailChunk000Sub000Block090Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part012] using hcert

def TailChunk000Sub000Block090Part013SupportExplicit : Finset ℕ :=
  ([3778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part013 : ℚ :=
  (222930854475 : ℚ) / 10590429268934656

def SurrogateDiagonalTailChunk000Sub000Block090Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3778
    = surrogateDiagTailX0RatChunk000Sub000Block090Part013

theorem surrogateDiagonalTailChunk000Sub000Block090Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part013] using hcert

def TailChunk000Sub000Block090Part014SupportExplicit : Finset ℕ :=
  ([3779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part014 : ℚ :=
  (223138140625 : ℚ) / 127354613419928082

def SurrogateDiagonalTailChunk000Sub000Block090Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3779
    = surrogateDiagTailX0RatChunk000Sub000Block090Part014

theorem surrogateDiagonalTailChunk000Sub000Block090Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part014] using hcert

def TailChunk000Sub000Block090Part015SupportExplicit : Finset ℕ :=
  ([3781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part015 : ℚ :=
  (858441081175 : ℚ) / 403438778604436608

def SurrogateDiagonalTailChunk000Sub000Block090Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3781
    = surrogateDiagTailX0RatChunk000Sub000Block090Part015

theorem surrogateDiagonalTailChunk000Sub000Block090Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part015] using hcert

def TailChunk000Sub000Block090Part016SupportExplicit : Finset ℕ :=
  ([3782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part016 : ℚ :=
  (28203607 : ℚ) / 1166633280000

def SurrogateDiagonalTailChunk000Sub000Block090Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3782
    = surrogateDiagTailX0RatChunk000Sub000Block090Part016

theorem surrogateDiagonalTailChunk000Sub000Block090Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part016] using hcert

def TailChunk000Sub000Block090Part017SupportExplicit : Finset ℕ :=
  ([3783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part017 : ℚ :=
  (160861292275 : ℚ) / 17615572678213632

def SurrogateDiagonalTailChunk000Sub000Block090Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3783
    = surrogateDiagTailX0RatChunk000Sub000Block090Part017

theorem surrogateDiagonalTailChunk000Sub000Block090Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part017] using hcert

def TailChunk000Sub000Block090Part018SupportExplicit : Finset ℕ :=
  ([3785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part018 : ℚ :=
  (262413414425 : ℚ) / 69699995728183296

def SurrogateDiagonalTailChunk000Sub000Block090Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3785
    = surrogateDiagTailX0RatChunk000Sub000Block090Part018

theorem surrogateDiagonalTailChunk000Sub000Block090Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part018] using hcert

def TailChunk000Sub000Block090Part019SupportExplicit : Finset ℕ :=
  ([3786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part019 : ℚ :=
  (497087749 : ℚ) / 9003492338400

def SurrogateDiagonalTailChunk000Sub000Block090Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3786
    = surrogateDiagTailX0RatChunk000Sub000Block090Part019

theorem surrogateDiagonalTailChunk000Sub000Block090Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part019] using hcert

def TailChunk000Sub000Block090Part020SupportExplicit : Finset ℕ :=
  ([3787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part020 : ℚ :=
  (32156715553 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block090Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3787
    = surrogateDiagTailX0RatChunk000Sub000Block090Part020

theorem surrogateDiagonalTailChunk000Sub000Block090Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part020] using hcert

def TailChunk000Sub000Block090Part021SupportExplicit : Finset ℕ :=
  ([3790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part021 : ℚ :=
  (519298608925 : ℚ) / 13068749199034368

def SurrogateDiagonalTailChunk000Sub000Block090Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3790
    = surrogateDiagTailX0RatChunk000Sub000Block090Part021

theorem surrogateDiagonalTailChunk000Sub000Block090Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part021] using hcert

def TailChunk000Sub000Block090Part022SupportExplicit : Finset ℕ :=
  ([3791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part022 : ℚ :=
  (547965652025 : ℚ) / 132677546722983936

def SurrogateDiagonalTailChunk000Sub000Block090Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3791
    = surrogateDiagTailX0RatChunk000Sub000Block090Part022

theorem surrogateDiagonalTailChunk000Sub000Block090Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part022] using hcert

def TailChunk000Sub000Block090Part023SupportExplicit : Finset ℕ :=
  ([3793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part023 : ℚ :=
  (1797996453775 : ℚ) / 517011464570830848

def SurrogateDiagonalTailChunk000Sub000Block090Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3793
    = surrogateDiagTailX0RatChunk000Sub000Block090Part023

theorem surrogateDiagonalTailChunk000Sub000Block090Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part023] using hcert

def TailChunk000Sub000Block090Part024SupportExplicit : Finset ℕ :=
  ([3794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block090Part024 : ℚ :=
  (69430819 : ℚ) / 2126189152800

def SurrogateDiagonalTailChunk000Sub000Block090Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3794
    = surrogateDiagTailX0RatChunk000Sub000Block090Part024

theorem surrogateDiagonalTailChunk000Sub000Block090Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block090Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block090Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block090Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block090Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block090Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block090HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block090Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block090Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block090Part000
    + surrogateDiagTailX0RatChunk000Sub000Block090Part001
    + surrogateDiagTailX0RatChunk000Sub000Block090Part002
    + surrogateDiagTailX0RatChunk000Sub000Block090Part003
    + surrogateDiagTailX0RatChunk000Sub000Block090Part004
    + surrogateDiagTailX0RatChunk000Sub000Block090Part005
    + surrogateDiagTailX0RatChunk000Sub000Block090Part006
    + surrogateDiagTailX0RatChunk000Sub000Block090Part007
    + surrogateDiagTailX0RatChunk000Sub000Block090Part008
    + surrogateDiagTailX0RatChunk000Sub000Block090Part009

def surrogateDiagonalTailChunk000Sub000Block090MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block090Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block090Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block090Part010
    + surrogateDiagTailX0RatChunk000Sub000Block090Part011
    + surrogateDiagTailX0RatChunk000Sub000Block090Part012
    + surrogateDiagTailX0RatChunk000Sub000Block090Part013
    + surrogateDiagTailX0RatChunk000Sub000Block090Part014
    + surrogateDiagTailX0RatChunk000Sub000Block090Part015
    + surrogateDiagTailX0RatChunk000Sub000Block090Part016
    + surrogateDiagTailX0RatChunk000Sub000Block090Part017
    + surrogateDiagTailX0RatChunk000Sub000Block090Part018
    + surrogateDiagTailX0RatChunk000Sub000Block090Part019

def surrogateDiagonalTailChunk000Sub000Block090TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block090Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block090Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block090Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block090Part020
    + surrogateDiagTailX0RatChunk000Sub000Block090Part021
    + surrogateDiagTailX0RatChunk000Sub000Block090Part022
    + surrogateDiagTailX0RatChunk000Sub000Block090Part023
    + surrogateDiagTailX0RatChunk000Sub000Block090Part024

def surrogateDiagonalTailChunk000Sub000Block090Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block090HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block090MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block090TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block090 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block090Part000
    + surrogateDiagTailX0RatChunk000Sub000Block090Part001
    + surrogateDiagTailX0RatChunk000Sub000Block090Part002
    + surrogateDiagTailX0RatChunk000Sub000Block090Part003
    + surrogateDiagTailX0RatChunk000Sub000Block090Part004
    + surrogateDiagTailX0RatChunk000Sub000Block090Part005
    + surrogateDiagTailX0RatChunk000Sub000Block090Part006
    + surrogateDiagTailX0RatChunk000Sub000Block090Part007
    + surrogateDiagTailX0RatChunk000Sub000Block090Part008
    + surrogateDiagTailX0RatChunk000Sub000Block090Part009
    + surrogateDiagTailX0RatChunk000Sub000Block090Part010
    + surrogateDiagTailX0RatChunk000Sub000Block090Part011
    + surrogateDiagTailX0RatChunk000Sub000Block090Part012
    + surrogateDiagTailX0RatChunk000Sub000Block090Part013
    + surrogateDiagTailX0RatChunk000Sub000Block090Part014
    + surrogateDiagTailX0RatChunk000Sub000Block090Part015
    + surrogateDiagTailX0RatChunk000Sub000Block090Part016
    + surrogateDiagTailX0RatChunk000Sub000Block090Part017
    + surrogateDiagTailX0RatChunk000Sub000Block090Part018
    + surrogateDiagTailX0RatChunk000Sub000Block090Part019
    + surrogateDiagTailX0RatChunk000Sub000Block090Part020
    + surrogateDiagTailX0RatChunk000Sub000Block090Part021
    + surrogateDiagTailX0RatChunk000Sub000Block090Part022
    + surrogateDiagTailX0RatChunk000Sub000Block090Part023
    + surrogateDiagTailX0RatChunk000Sub000Block090Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block090_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block090Head + surrogateDiagTailX0RatChunk000Sub000Block090Mid + surrogateDiagTailX0RatChunk000Sub000Block090Tail =
      surrogateDiagTailX0RatChunk000Sub000Block090 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block090Head surrogateDiagTailX0RatChunk000Sub000Block090Mid surrogateDiagTailX0RatChunk000Sub000Block090Tail surrogateDiagTailX0RatChunk000Sub000Block090
  ring

def SurrogateDiagonalTailChunk000Sub000Block090HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block090HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block090Head

def SurrogateDiagonalTailChunk000Sub000Block090MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block090MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block090Mid

def SurrogateDiagonalTailChunk000Sub000Block090TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block090TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block090Tail

theorem surrogateDiagonalTailChunk000Sub000Block090_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block090HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block090MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block090TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block090Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block090 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block090HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block090MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block090TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block090Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block090_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
