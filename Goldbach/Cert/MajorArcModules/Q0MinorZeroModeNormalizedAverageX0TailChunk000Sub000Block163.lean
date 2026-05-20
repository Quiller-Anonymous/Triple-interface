import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [163,164). -/

/-- Block 163 covers tail-support indices [4075,4100) and q from 6753 to 6791. -/

def TailChunk000Sub000Block163Part000SupportExplicit : Finset ℕ :=
  ([6753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part000 : ℚ :=
  (12666216749 : ℚ) / 20507225625000000

def SurrogateDiagonalTailChunk000Sub000Block163Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6753
    = surrogateDiagTailX0RatChunk000Sub000Block163Part000

theorem surrogateDiagonalTailChunk000Sub000Block163Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part000] using hcert

def TailChunk000Sub000Block163Part001SupportExplicit : Finset ℕ :=
  ([6754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part001 : ℚ :=
  (360658697 : ℚ) / 116926053814656

def SurrogateDiagonalTailChunk000Sub000Block163Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6754
    = surrogateDiagTailX0RatChunk000Sub000Block163Part001

theorem surrogateDiagonalTailChunk000Sub000Block163Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part001] using hcert

def TailChunk000Sub000Block163Part002SupportExplicit : Finset ℕ :=
  ([6755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part002 : ℚ :=
  (482026076125 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub000Block163Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6755
    = surrogateDiagTailX0RatChunk000Sub000Block163Part002

theorem surrogateDiagonalTailChunk000Sub000Block163Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part002] using hcert

def TailChunk000Sub000Block163Part003SupportExplicit : Finset ℕ :=
  ([6757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part003 : ℚ :=
  (226434087975 : ℚ) / 371047643509817344

def SurrogateDiagonalTailChunk000Sub000Block163Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6757
    = surrogateDiagTailX0RatChunk000Sub000Block163Part003

theorem surrogateDiagonalTailChunk000Sub000Block163Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part003] using hcert

def TailChunk000Sub000Block163Part004SupportExplicit : Finset ℕ :=
  ([6758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part004 : ℚ :=
  (27075034949 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub000Block163Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6758
    = surrogateDiagTailX0RatChunk000Sub000Block163Part004

theorem surrogateDiagonalTailChunk000Sub000Block163Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part004] using hcert

def TailChunk000Sub000Block163Part005SupportExplicit : Finset ℕ :=
  ([6761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part005 : ℚ :=
  (1142778025 : ℚ) / 2088688299889152

def SurrogateDiagonalTailChunk000Sub000Block163Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6761
    = surrogateDiagTailX0RatChunk000Sub000Block163Part005

theorem surrogateDiagonalTailChunk000Sub000Block163Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part005] using hcert

def TailChunk000Sub000Block163Part006SupportExplicit : Finset ℕ :=
  ([6763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part006 : ℚ :=
  (714658890625 : ℚ) / 1306975760962825842

def SurrogateDiagonalTailChunk000Sub000Block163Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6763
    = surrogateDiagTailX0RatChunk000Sub000Block163Part006

theorem surrogateDiagonalTailChunk000Sub000Block163Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part006] using hcert

def TailChunk000Sub000Block163Part007SupportExplicit : Finset ℕ :=
  ([6765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part007 : ℚ :=
  (21816962357 : ℚ) / 5243928576000000

def SurrogateDiagonalTailChunk000Sub000Block163Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6765
    = surrogateDiagTailX0RatChunk000Sub000Block163Part007

theorem surrogateDiagonalTailChunk000Sub000Block163Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part007] using hcert

def TailChunk000Sub000Block163Part008SupportExplicit : Finset ℕ :=
  ([6766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part008 : ℚ :=
  (219345239875 : ℚ) / 41977473890254848

def SurrogateDiagonalTailChunk000Sub000Block163Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6766
    = surrogateDiagTailX0RatChunk000Sub000Block163Part008

theorem surrogateDiagonalTailChunk000Sub000Block163Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part008] using hcert

def TailChunk000Sub000Block163Part009SupportExplicit : Finset ℕ :=
  ([6767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part009 : ℚ :=
  (55481903993 : ℚ) / 94892654736000000

def SurrogateDiagonalTailChunk000Sub000Block163Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6767
    = surrogateDiagTailX0RatChunk000Sub000Block163Part009

theorem surrogateDiagonalTailChunk000Sub000Block163Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part009] using hcert

def TailChunk000Sub000Block163Part010SupportExplicit : Finset ℕ :=
  ([6769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part010 : ℚ :=
  (2335181990275 : ℚ) / 2821891855406617728

def SurrogateDiagonalTailChunk000Sub000Block163Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6769
    = surrogateDiagTailX0RatChunk000Sub000Block163Part010

theorem surrogateDiagonalTailChunk000Sub000Block163Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part010] using hcert

def TailChunk000Sub000Block163Part011SupportExplicit : Finset ℕ :=
  ([6770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part011 : ℚ :=
  (1058165929525 : ℚ) / 133676051192905728

def SurrogateDiagonalTailChunk000Sub000Block163Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6770
    = surrogateDiagTailX0RatChunk000Sub000Block163Part011

theorem surrogateDiagonalTailChunk000Sub000Block163Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part011] using hcert

def TailChunk000Sub000Block163Part012SupportExplicit : Finset ℕ :=
  ([6771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part012 : ℚ :=
  (12126794669 : ℚ) / 6967096615895040

def SurrogateDiagonalTailChunk000Sub000Block163Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6771
    = surrogateDiagTailX0RatChunk000Sub000Block163Part012

theorem surrogateDiagonalTailChunk000Sub000Block163Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part012] using hcert

def TailChunk000Sub000Block163Part013SupportExplicit : Finset ℕ :=
  ([6773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part013 : ℚ :=
  (103597257811 : ℚ) / 151643992109875200

def SurrogateDiagonalTailChunk000Sub000Block163Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6773
    = surrogateDiagTailX0RatChunk000Sub000Block163Part013

theorem surrogateDiagonalTailChunk000Sub000Block163Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part013] using hcert

def TailChunk000Sub000Block163Part014SupportExplicit : Finset ℕ :=
  ([6774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part014 : ℚ :=
  (875547582175 : ℚ) / 64771393426587648

def SurrogateDiagonalTailChunk000Sub000Block163Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6774
    = surrogateDiagTailX0RatChunk000Sub000Block163Part014

theorem surrogateDiagonalTailChunk000Sub000Block163Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part014] using hcert

def TailChunk000Sub000Block163Part015SupportExplicit : Finset ℕ :=
  ([6778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part015 : ℚ :=
  (1435377991975 : ℚ) / 329458309386019968

def SurrogateDiagonalTailChunk000Sub000Block163Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6778
    = surrogateDiagTailX0RatChunk000Sub000Block163Part015

theorem surrogateDiagonalTailChunk000Sub000Block163Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part015] using hcert

def TailChunk000Sub000Block163Part016SupportExplicit : Finset ℕ :=
  ([6779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part016 : ℚ :=
  (718044390625 : ℚ) / 1319389809927356082

def SurrogateDiagonalTailChunk000Sub000Block163Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6779
    = surrogateDiagTailX0RatChunk000Sub000Block163Part016

theorem surrogateDiagonalTailChunk000Sub000Block163Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part016] using hcert

def TailChunk000Sub000Block163Part017SupportExplicit : Finset ℕ :=
  ([6781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part017 : ℚ :=
  (1149549025 : ℚ) / 2113516417319712

def SurrogateDiagonalTailChunk000Sub000Block163Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6781
    = surrogateDiagTailX0RatChunk000Sub000Block163Part017

theorem surrogateDiagonalTailChunk000Sub000Block163Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part017] using hcert

def TailChunk000Sub000Block163Part018SupportExplicit : Finset ℕ :=
  ([6782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part018 : ℚ :=
  (287472025 : ℚ) / 132094776082482

def SurrogateDiagonalTailChunk000Sub000Block163Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6782
    = surrogateDiagTailX0RatChunk000Sub000Block163Part018

theorem surrogateDiagonalTailChunk000Sub000Block163Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part018] using hcert

def TailChunk000Sub000Block163Part019SupportExplicit : Finset ℕ :=
  ([6783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part019 : ℚ :=
  (99857304275 : ℚ) / 29726278894485504

def SurrogateDiagonalTailChunk000Sub000Block163Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6783
    = surrogateDiagTailX0RatChunk000Sub000Block163Part019

theorem surrogateDiagonalTailChunk000Sub000Block163Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part019] using hcert

def TailChunk000Sub000Block163Part020SupportExplicit : Finset ℕ :=
  ([6785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part020 : ℚ :=
  (2028464625175 : ℚ) / 1696951858171772928

def SurrogateDiagonalTailChunk000Sub000Block163Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6785
    = surrogateDiagTailX0RatChunk000Sub000Block163Part020

theorem surrogateDiagonalTailChunk000Sub000Block163Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part020] using hcert

def TailChunk000Sub000Block163Part021SupportExplicit : Finset ℕ :=
  ([6787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part021 : ℚ :=
  (101647947661 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub000Block163Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6787
    = surrogateDiagTailX0RatChunk000Sub000Block163Part021

theorem surrogateDiagonalTailChunk000Sub000Block163Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part021] using hcert

def TailChunk000Sub000Block163Part022SupportExplicit : Finset ℕ :=
  ([6789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part022 : ℚ :=
  (72394476889 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block163Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6789
    = surrogateDiagTailX0RatChunk000Sub000Block163Part022

theorem surrogateDiagonalTailChunk000Sub000Block163Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part022] using hcert

def TailChunk000Sub000Block163Part023SupportExplicit : Finset ℕ :=
  ([6790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part023 : ℚ :=
  (576036452275 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block163Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6790
    = surrogateDiagTailX0RatChunk000Sub000Block163Part023

theorem surrogateDiagonalTailChunk000Sub000Block163Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part023] using hcert

def TailChunk000Sub000Block163Part024SupportExplicit : Finset ℕ :=
  ([6791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block163Part024 : ℚ :=
  (1152942025 : ℚ) / 2126013154417362

def SurrogateDiagonalTailChunk000Sub000Block163Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6791
    = surrogateDiagTailX0RatChunk000Sub000Block163Part024

theorem surrogateDiagonalTailChunk000Sub000Block163Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block163Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block163Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block163Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block163Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block163Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block163HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block163Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block163Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part000
    + surrogateDiagTailX0RatChunk000Sub000Block163Part001
    + surrogateDiagTailX0RatChunk000Sub000Block163Part002
    + surrogateDiagTailX0RatChunk000Sub000Block163Part003
    + surrogateDiagTailX0RatChunk000Sub000Block163Part004
    + surrogateDiagTailX0RatChunk000Sub000Block163Part005
    + surrogateDiagTailX0RatChunk000Sub000Block163Part006
    + surrogateDiagTailX0RatChunk000Sub000Block163Part007
    + surrogateDiagTailX0RatChunk000Sub000Block163Part008
    + surrogateDiagTailX0RatChunk000Sub000Block163Part009

def surrogateDiagonalTailChunk000Sub000Block163MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block163Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block163Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part010
    + surrogateDiagTailX0RatChunk000Sub000Block163Part011
    + surrogateDiagTailX0RatChunk000Sub000Block163Part012
    + surrogateDiagTailX0RatChunk000Sub000Block163Part013
    + surrogateDiagTailX0RatChunk000Sub000Block163Part014
    + surrogateDiagTailX0RatChunk000Sub000Block163Part015
    + surrogateDiagTailX0RatChunk000Sub000Block163Part016
    + surrogateDiagTailX0RatChunk000Sub000Block163Part017
    + surrogateDiagTailX0RatChunk000Sub000Block163Part018
    + surrogateDiagTailX0RatChunk000Sub000Block163Part019

def surrogateDiagonalTailChunk000Sub000Block163TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block163Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block163Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block163Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part020
    + surrogateDiagTailX0RatChunk000Sub000Block163Part021
    + surrogateDiagTailX0RatChunk000Sub000Block163Part022
    + surrogateDiagTailX0RatChunk000Sub000Block163Part023
    + surrogateDiagTailX0RatChunk000Sub000Block163Part024

def surrogateDiagonalTailChunk000Sub000Block163Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block163HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block163MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block163TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block163 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block163Part000
    + surrogateDiagTailX0RatChunk000Sub000Block163Part001
    + surrogateDiagTailX0RatChunk000Sub000Block163Part002
    + surrogateDiagTailX0RatChunk000Sub000Block163Part003
    + surrogateDiagTailX0RatChunk000Sub000Block163Part004
    + surrogateDiagTailX0RatChunk000Sub000Block163Part005
    + surrogateDiagTailX0RatChunk000Sub000Block163Part006
    + surrogateDiagTailX0RatChunk000Sub000Block163Part007
    + surrogateDiagTailX0RatChunk000Sub000Block163Part008
    + surrogateDiagTailX0RatChunk000Sub000Block163Part009
    + surrogateDiagTailX0RatChunk000Sub000Block163Part010
    + surrogateDiagTailX0RatChunk000Sub000Block163Part011
    + surrogateDiagTailX0RatChunk000Sub000Block163Part012
    + surrogateDiagTailX0RatChunk000Sub000Block163Part013
    + surrogateDiagTailX0RatChunk000Sub000Block163Part014
    + surrogateDiagTailX0RatChunk000Sub000Block163Part015
    + surrogateDiagTailX0RatChunk000Sub000Block163Part016
    + surrogateDiagTailX0RatChunk000Sub000Block163Part017
    + surrogateDiagTailX0RatChunk000Sub000Block163Part018
    + surrogateDiagTailX0RatChunk000Sub000Block163Part019
    + surrogateDiagTailX0RatChunk000Sub000Block163Part020
    + surrogateDiagTailX0RatChunk000Sub000Block163Part021
    + surrogateDiagTailX0RatChunk000Sub000Block163Part022
    + surrogateDiagTailX0RatChunk000Sub000Block163Part023
    + surrogateDiagTailX0RatChunk000Sub000Block163Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block163_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block163Head + surrogateDiagTailX0RatChunk000Sub000Block163Mid + surrogateDiagTailX0RatChunk000Sub000Block163Tail =
      surrogateDiagTailX0RatChunk000Sub000Block163 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block163Head surrogateDiagTailX0RatChunk000Sub000Block163Mid surrogateDiagTailX0RatChunk000Sub000Block163Tail surrogateDiagTailX0RatChunk000Sub000Block163
  ring

def SurrogateDiagonalTailChunk000Sub000Block163HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block163HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block163Head

def SurrogateDiagonalTailChunk000Sub000Block163MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block163MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block163Mid

def SurrogateDiagonalTailChunk000Sub000Block163TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block163TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block163Tail

theorem surrogateDiagonalTailChunk000Sub000Block163_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block163HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block163MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block163TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block163Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block163 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block163HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block163MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block163TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block163Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block163_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
