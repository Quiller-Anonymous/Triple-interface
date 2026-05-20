import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [60,70). -/

/-- Block 060 covers tail-support indices [6500,6525) and q from 10742 to 10783. -/

def TailChunk000Sub001Block060Part000SupportExplicit : Finset ℕ :=
  ([10742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part000 : ℚ :=
  (69673210039 : ℚ) / 73130783232000000

def SurrogateDiagonalTailChunk000Sub001Block060Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10742
    = surrogateDiagTailX0RatChunk000Sub001Block060Part000

theorem surrogateDiagonalTailChunk000Sub001Block060Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part000] using hcert

def TailChunk000Sub001Block060Part001SupportExplicit : Finset ℕ :=
  ([10743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part001 : ℚ :=
  (80127813359 : ℚ) / 131434368785433600

def SurrogateDiagonalTailChunk000Sub001Block060Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10743
    = surrogateDiagTailX0RatChunk000Sub001Block060Part001

theorem surrogateDiagonalTailChunk000Sub001Block060Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part001] using hcert

def TailChunk000Sub001Block060Part002SupportExplicit : Finset ℕ :=
  ([10745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part002 : ℚ :=
  (774097052875 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub001Block060Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10745
    = surrogateDiagTailX0RatChunk000Sub001Block060Part002

theorem surrogateDiagonalTailChunk000Sub001Block060Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part002] using hcert

def TailChunk000Sub001Block060Part003SupportExplicit : Finset ℕ :=
  ([10747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part003 : ℚ :=
  (60113789 : ℚ) / 4537912579915776

def SurrogateDiagonalTailChunk000Sub001Block060Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10747
    = surrogateDiagTailX0RatChunk000Sub001Block060Part003

theorem surrogateDiagonalTailChunk000Sub001Block060Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part003] using hcert

def TailChunk000Sub001Block060Part004SupportExplicit : Finset ℕ :=
  ([10749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part004 : ℚ :=
  (401272673975 : ℚ) / 3293208077196976704

def SurrogateDiagonalTailChunk000Sub001Block060Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10749
    = surrogateDiagTailX0RatChunk000Sub001Block060Part004

theorem surrogateDiagonalTailChunk000Sub001Block060Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part004] using hcert

def TailChunk000Sub001Block060Part005SupportExplicit : Finset ℕ :=
  ([10751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part005 : ℚ :=
  (259350281875 : ℚ) / 24136374312324384768

def SurrogateDiagonalTailChunk000Sub001Block060Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10751
    = surrogateDiagTailX0RatChunk000Sub001Block060Part005

theorem surrogateDiagonalTailChunk000Sub001Block060Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part005] using hcert

def TailChunk000Sub001Block060Part006SupportExplicit : Finset ℕ :=
  ([10753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block060Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10753
    = surrogateDiagTailX0RatChunk000Sub001Block060Part006

theorem surrogateDiagonalTailChunk000Sub001Block060Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part006] using hcert

def TailChunk000Sub001Block060Part007SupportExplicit : Finset ℕ :=
  ([10754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part007 : ℚ :=
  (850397437025 : ℚ) / 830009984905940544

def SurrogateDiagonalTailChunk000Sub001Block060Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10754
    = surrogateDiagTailX0RatChunk000Sub001Block060Part007

theorem surrogateDiagonalTailChunk000Sub001Block060Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part007] using hcert

def TailChunk000Sub001Block060Part008SupportExplicit : Finset ℕ :=
  ([10757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part008 : ℚ :=
  (242557061 : ℚ) / 58055887512531360

def SurrogateDiagonalTailChunk000Sub001Block060Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10757
    = surrogateDiagTailX0RatChunk000Sub001Block060Part008

theorem surrogateDiagonalTailChunk000Sub001Block060Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part008] using hcert

def TailChunk000Sub001Block060Part009SupportExplicit : Finset ℕ :=
  ([10758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part009 : ℚ :=
  (21616011563 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub001Block060Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10758
    = surrogateDiagTailX0RatChunk000Sub001Block060Part009

theorem surrogateDiagonalTailChunk000Sub001Block060Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part009] using hcert

def TailChunk000Sub001Block060Part010SupportExplicit : Finset ℕ :=
  ([10759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part010 : ℚ :=
  (273450064625 : ℚ) / 7281944501116207104

def SurrogateDiagonalTailChunk000Sub001Block060Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10759
    = surrogateDiagTailX0RatChunk000Sub001Block060Part010

theorem surrogateDiagonalTailChunk000Sub001Block060Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part010] using hcert

def TailChunk000Sub001Block060Part011SupportExplicit : Finset ℕ :=
  ([10761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part011 : ℚ :=
  (6761035037 : ℚ) / 40793778935562240

def SurrogateDiagonalTailChunk000Sub001Block060Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10761
    = surrogateDiagTailX0RatChunk000Sub001Block060Part011

theorem surrogateDiagonalTailChunk000Sub001Block060Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part011] using hcert

def TailChunk000Sub001Block060Part012SupportExplicit : Finset ℕ :=
  ([10762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part012 : ℚ :=
  (723879025 : ℚ) / 837945847018272

def SurrogateDiagonalTailChunk000Sub001Block060Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10762
    = surrogateDiagTailX0RatChunk000Sub001Block060Part012

theorem surrogateDiagonalTailChunk000Sub001Block060Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part012] using hcert

def TailChunk000Sub001Block060Part013SupportExplicit : Finset ℕ :=
  ([10763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part013 : ℚ :=
  (890659825 : ℚ) / 315156552129724608

def SurrogateDiagonalTailChunk000Sub001Block060Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10763
    = surrogateDiagTailX0RatChunk000Sub001Block060Part013

theorem surrogateDiagonalTailChunk000Sub001Block060Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part013] using hcert

def TailChunk000Sub001Block060Part014SupportExplicit : Finset ℕ :=
  ([10765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part014 : ℚ :=
  (580022701525 : ℚ) / 13728904757547368448

def SurrogateDiagonalTailChunk000Sub001Block060Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10765
    = surrogateDiagTailX0RatChunk000Sub001Block060Part014

theorem surrogateDiagonalTailChunk000Sub001Block060Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part014] using hcert

def TailChunk000Sub001Block060Part015SupportExplicit : Finset ℕ :=
  ([10766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part015 : ℚ :=
  (1513591084375 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub001Block060Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10766
    = surrogateDiagTailX0RatChunk000Sub001Block060Part015

theorem surrogateDiagonalTailChunk000Sub001Block060Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part015] using hcert

def TailChunk000Sub001Block060Part016SupportExplicit : Finset ℕ :=
  ([10767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part016 : ℚ :=
  (30653776925 : ℚ) / 211386872138563584

def SurrogateDiagonalTailChunk000Sub001Block060Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10767
    = surrogateDiagTailX0RatChunk000Sub001Block060Part016

theorem surrogateDiagonalTailChunk000Sub001Block060Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part016] using hcert

def TailChunk000Sub001Block060Part017SupportExplicit : Finset ℕ :=
  ([10770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part017 : ℚ :=
  (931861586575 : ℚ) / 168235992045355008

def SurrogateDiagonalTailChunk000Sub001Block060Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10770
    = surrogateDiagTailX0RatChunk000Sub001Block060Part017

theorem surrogateDiagonalTailChunk000Sub001Block060Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part017] using hcert

def TailChunk000Sub001Block060Part018SupportExplicit : Finset ℕ :=
  ([10771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block060Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10771
    = surrogateDiagTailX0RatChunk000Sub001Block060Part018

theorem surrogateDiagonalTailChunk000Sub001Block060Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part018] using hcert

def TailChunk000Sub001Block060Part019SupportExplicit : Finset ℕ :=
  ([10774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part019 : ℚ :=
  (453433890625 : ℚ) / 526056345811126002

def SurrogateDiagonalTailChunk000Sub001Block060Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10774
    = surrogateDiagTailX0RatChunk000Sub001Block060Part019

theorem surrogateDiagonalTailChunk000Sub001Block060Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part019] using hcert

def TailChunk000Sub001Block060Part020SupportExplicit : Finset ℕ :=
  ([10777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part020 : ℚ :=
  (260589538375 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk000Sub001Block060Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10777
    = surrogateDiagTailX0RatChunk000Sub001Block060Part020

theorem surrogateDiagonalTailChunk000Sub001Block060Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part020] using hcert

def TailChunk000Sub001Block060Part021SupportExplicit : Finset ℕ :=
  ([10778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part021 : ℚ :=
  (848315114225 : ℚ) / 817005771173658624

def SurrogateDiagonalTailChunk000Sub001Block060Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10778
    = surrogateDiagTailX0RatChunk000Sub001Block060Part021

theorem surrogateDiagonalTailChunk000Sub001Block060Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part021] using hcert

def TailChunk000Sub001Block060Part022SupportExplicit : Finset ℕ :=
  ([10779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part022 : ℚ :=
  (201757274425 : ℚ) / 1665068719867502592

def SurrogateDiagonalTailChunk000Sub001Block060Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10779
    = surrogateDiagTailX0RatChunk000Sub001Block060Part022

theorem surrogateDiagonalTailChunk000Sub001Block060Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part022] using hcert

def TailChunk000Sub001Block060Part023SupportExplicit : Finset ℕ :=
  ([10781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block060Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10781
    = surrogateDiagTailX0RatChunk000Sub001Block060Part023

theorem surrogateDiagonalTailChunk000Sub001Block060Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part023] using hcert

def TailChunk000Sub001Block060Part024SupportExplicit : Finset ℕ :=
  ([10783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block060Part024 : ℚ :=
  (624833691 : ℚ) / 201085488458547200

def SurrogateDiagonalTailChunk000Sub001Block060Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10783
    = surrogateDiagTailX0RatChunk000Sub001Block060Part024

theorem surrogateDiagonalTailChunk000Sub001Block060Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block060Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block060Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block060Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block060Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block060Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block060HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block060Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block060Part000
    + surrogateDiagTailX0RatChunk000Sub001Block060Part001
    + surrogateDiagTailX0RatChunk000Sub001Block060Part002
    + surrogateDiagTailX0RatChunk000Sub001Block060Part003
    + surrogateDiagTailX0RatChunk000Sub001Block060Part004
    + surrogateDiagTailX0RatChunk000Sub001Block060Part005
    + surrogateDiagTailX0RatChunk000Sub001Block060Part006
    + surrogateDiagTailX0RatChunk000Sub001Block060Part007
    + surrogateDiagTailX0RatChunk000Sub001Block060Part008
    + surrogateDiagTailX0RatChunk000Sub001Block060Part009

def surrogateDiagonalTailChunk000Sub001Block060MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block060Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block060Part010
    + surrogateDiagTailX0RatChunk000Sub001Block060Part011
    + surrogateDiagTailX0RatChunk000Sub001Block060Part012
    + surrogateDiagTailX0RatChunk000Sub001Block060Part013
    + surrogateDiagTailX0RatChunk000Sub001Block060Part014
    + surrogateDiagTailX0RatChunk000Sub001Block060Part015
    + surrogateDiagTailX0RatChunk000Sub001Block060Part016
    + surrogateDiagTailX0RatChunk000Sub001Block060Part017
    + surrogateDiagTailX0RatChunk000Sub001Block060Part018
    + surrogateDiagTailX0RatChunk000Sub001Block060Part019

def surrogateDiagonalTailChunk000Sub001Block060TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block060Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block060Part020
    + surrogateDiagTailX0RatChunk000Sub001Block060Part021
    + surrogateDiagTailX0RatChunk000Sub001Block060Part022
    + surrogateDiagTailX0RatChunk000Sub001Block060Part023
    + surrogateDiagTailX0RatChunk000Sub001Block060Part024

def surrogateDiagonalTailChunk000Sub001Block060Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block060HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block060MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block060TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block060 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block060Part000
    + surrogateDiagTailX0RatChunk000Sub001Block060Part001
    + surrogateDiagTailX0RatChunk000Sub001Block060Part002
    + surrogateDiagTailX0RatChunk000Sub001Block060Part003
    + surrogateDiagTailX0RatChunk000Sub001Block060Part004
    + surrogateDiagTailX0RatChunk000Sub001Block060Part005
    + surrogateDiagTailX0RatChunk000Sub001Block060Part006
    + surrogateDiagTailX0RatChunk000Sub001Block060Part007
    + surrogateDiagTailX0RatChunk000Sub001Block060Part008
    + surrogateDiagTailX0RatChunk000Sub001Block060Part009
    + surrogateDiagTailX0RatChunk000Sub001Block060Part010
    + surrogateDiagTailX0RatChunk000Sub001Block060Part011
    + surrogateDiagTailX0RatChunk000Sub001Block060Part012
    + surrogateDiagTailX0RatChunk000Sub001Block060Part013
    + surrogateDiagTailX0RatChunk000Sub001Block060Part014
    + surrogateDiagTailX0RatChunk000Sub001Block060Part015
    + surrogateDiagTailX0RatChunk000Sub001Block060Part016
    + surrogateDiagTailX0RatChunk000Sub001Block060Part017
    + surrogateDiagTailX0RatChunk000Sub001Block060Part018
    + surrogateDiagTailX0RatChunk000Sub001Block060Part019
    + surrogateDiagTailX0RatChunk000Sub001Block060Part020
    + surrogateDiagTailX0RatChunk000Sub001Block060Part021
    + surrogateDiagTailX0RatChunk000Sub001Block060Part022
    + surrogateDiagTailX0RatChunk000Sub001Block060Part023
    + surrogateDiagTailX0RatChunk000Sub001Block060Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block060_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block060Head + surrogateDiagTailX0RatChunk000Sub001Block060Mid + surrogateDiagTailX0RatChunk000Sub001Block060Tail =
      surrogateDiagTailX0RatChunk000Sub001Block060 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block060Head surrogateDiagTailX0RatChunk000Sub001Block060Mid surrogateDiagTailX0RatChunk000Sub001Block060Tail surrogateDiagTailX0RatChunk000Sub001Block060
  ring

def SurrogateDiagonalTailChunk000Sub001Block060HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block060HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block060Head

def SurrogateDiagonalTailChunk000Sub001Block060MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block060MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block060Mid

def SurrogateDiagonalTailChunk000Sub001Block060TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block060TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block060Tail

theorem surrogateDiagonalTailChunk000Sub001Block060_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block060HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block060MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block060TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block060Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block060 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block060HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block060MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block060TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block060Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block060_eq_head_add_mid_add_tail

/-- Block 061 covers tail-support indices [6525,6550) and q from 10785 to 10821. -/

def TailChunk000Sub001Block061Part000SupportExplicit : Finset ℕ :=
  ([10785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part000 : ℚ :=
  (1001210821075 : ℚ) / 2721977831167131648

def SurrogateDiagonalTailChunk000Sub001Block061Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10785
    = surrogateDiagTailX0RatChunk000Sub001Block061Part000

theorem surrogateDiagonalTailChunk000Sub001Block061Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part000] using hcert

def TailChunk000Sub001Block061Part001SupportExplicit : Finset ℕ :=
  ([10786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part001 : ℚ :=
  (454444515625 : ℚ) / 528404371232858112

def SurrogateDiagonalTailChunk000Sub001Block061Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10786
    = surrogateDiagTailX0RatChunk000Sub001Block061Part001

theorem surrogateDiagonalTailChunk000Sub001Block061Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part001] using hcert

def TailChunk000Sub001Block061Part002SupportExplicit : Finset ℕ :=
  ([10787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part002 : ℚ :=
  (50103457325 : ℚ) / 1309500415967090688

def SurrogateDiagonalTailChunk000Sub001Block061Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10787
    = surrogateDiagTailX0RatChunk000Sub001Block061Part002

theorem surrogateDiagonalTailChunk000Sub001Block061Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part002] using hcert

def TailChunk000Sub001Block061Part003SupportExplicit : Finset ℕ :=
  ([10789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block061Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10789
    = surrogateDiagTailX0RatChunk000Sub001Block061Part003

theorem surrogateDiagonalTailChunk000Sub001Block061Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part003] using hcert

def TailChunk000Sub001Block061Part004SupportExplicit : Finset ℕ :=
  ([10790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part004 : ℚ :=
  (164732439875 : ℚ) / 75016574837784576

def SurrogateDiagonalTailChunk000Sub001Block061Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10790
    = surrogateDiagTailX0RatChunk000Sub001Block061Part004

theorem surrogateDiagonalTailChunk000Sub001Block061Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part004] using hcert

def TailChunk000Sub001Block061Part005SupportExplicit : Finset ℕ :=
  ([10793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part005 : ℚ :=
  (871516669 : ℚ) / 303937337812500000

def SurrogateDiagonalTailChunk000Sub001Block061Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10793
    = surrogateDiagTailX0RatChunk000Sub001Block061Part005

theorem surrogateDiagonalTailChunk000Sub001Block061Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part005] using hcert

def TailChunk000Sub001Block061Part006SupportExplicit : Finset ℕ :=
  ([10794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part006 : ℚ :=
  (1015647700975 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub001Block061Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10794
    = surrogateDiagTailX0RatChunk000Sub001Block061Part006

theorem surrogateDiagonalTailChunk000Sub001Block061Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part006] using hcert

def TailChunk000Sub001Block061Part007SupportExplicit : Finset ℕ :=
  ([10795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part007 : ℚ :=
  (2110194725 : ℚ) / 32635023148449792

def SurrogateDiagonalTailChunk000Sub001Block061Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10795
    = surrogateDiagTailX0RatChunk000Sub001Block061Part007

theorem surrogateDiagonalTailChunk000Sub001Block061Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part007] using hcert

def TailChunk000Sub001Block061Part008SupportExplicit : Finset ℕ :=
  ([10797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part008 : ℚ :=
  (31720622981 : ℚ) / 117352896414105600

def SurrogateDiagonalTailChunk000Sub001Block061Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10797
    = surrogateDiagTailX0RatChunk000Sub001Block061Part008

theorem surrogateDiagonalTailChunk000Sub001Block061Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part008] using hcert

def TailChunk000Sub001Block061Part009SupportExplicit : Finset ℕ :=
  ([10798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part009 : ℚ :=
  (455456265625 : ℚ) / 530760248115468402

def SurrogateDiagonalTailChunk000Sub001Block061Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10798
    = surrogateDiagTailX0RatChunk000Sub001Block061Part009

theorem surrogateDiagonalTailChunk000Sub001Block061Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part009] using hcert

def TailChunk000Sub001Block061Part010SupportExplicit : Finset ℕ :=
  ([10799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block061Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10799
    = surrogateDiagTailX0RatChunk000Sub001Block061Part010

theorem surrogateDiagonalTailChunk000Sub001Block061Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part010] using hcert

def TailChunk000Sub001Block061Part011SupportExplicit : Finset ℕ :=
  ([10801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part011 : ℚ :=
  (8287537825 : ℚ) / 339293543521436352

def SurrogateDiagonalTailChunk000Sub001Block061Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10801
    = surrogateDiagTailX0RatChunk000Sub001Block061Part011

theorem surrogateDiagonalTailChunk000Sub001Block061Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part011] using hcert

def TailChunk000Sub001Block061Part012SupportExplicit : Finset ℕ :=
  ([10802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part012 : ℚ :=
  (32782542167 : ℚ) / 28829769801000000

def SurrogateDiagonalTailChunk000Sub001Block061Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10802
    = surrogateDiagTailX0RatChunk000Sub001Block061Part012

theorem surrogateDiagonalTailChunk000Sub001Block061Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part012] using hcert

def TailChunk000Sub001Block061Part013SupportExplicit : Finset ℕ :=
  ([10803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part013 : ℚ :=
  (1540182019975 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk000Sub001Block061Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10803
    = surrogateDiagTailX0RatChunk000Sub001Block061Part013

theorem surrogateDiagonalTailChunk000Sub001Block061Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part013] using hcert

def TailChunk000Sub001Block061Part014SupportExplicit : Finset ℕ :=
  ([10805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part014 : ℚ :=
  (7791117823 : ℚ) / 185789243090534400

def SurrogateDiagonalTailChunk000Sub001Block061Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10805
    = surrogateDiagTailX0RatChunk000Sub001Block061Part014

theorem surrogateDiagonalTailChunk000Sub001Block061Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part014] using hcert

def TailChunk000Sub001Block061Part015SupportExplicit : Finset ℕ :=
  ([10806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part015 : ℚ :=
  (1620833 : ℚ) / 559872000000

def SurrogateDiagonalTailChunk000Sub001Block061Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10806
    = surrogateDiagTailX0RatChunk000Sub001Block061Part015

theorem surrogateDiagonalTailChunk000Sub001Block061Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part015] using hcert

def TailChunk000Sub001Block061Part016SupportExplicit : Finset ℕ :=
  ([10807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part016 : ℚ :=
  (160632091 : ℚ) / 78920590962000000

def SurrogateDiagonalTailChunk000Sub001Block061Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10807
    = surrogateDiagTailX0RatChunk000Sub001Block061Part016

theorem surrogateDiagonalTailChunk000Sub001Block061Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part016] using hcert

def TailChunk000Sub001Block061Part017SupportExplicit : Finset ℕ :=
  ([10810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part017 : ℚ :=
  (453526560825 : ℚ) / 223803884143476736

def SurrogateDiagonalTailChunk000Sub001Block061Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10810
    = surrogateDiagTailX0RatChunk000Sub001Block061Part017

theorem surrogateDiagonalTailChunk000Sub001Block061Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part017] using hcert

def TailChunk000Sub001Block061Part018SupportExplicit : Finset ℕ :=
  ([10811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part018 : ℚ :=
  (93403717925 : ℚ) / 13660928757662367744

def SurrogateDiagonalTailChunk000Sub001Block061Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10811
    = surrogateDiagTailX0RatChunk000Sub001Block061Part018

theorem surrogateDiagonalTailChunk000Sub001Block061Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part018] using hcert

def TailChunk000Sub001Block061Part019SupportExplicit : Finset ℕ :=
  ([10813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part019 : ℚ :=
  (243389801 : ℚ) / 18602135222627904

def SurrogateDiagonalTailChunk000Sub001Block061Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10813
    = surrogateDiagTailX0RatChunk000Sub001Block061Part019

theorem surrogateDiagonalTailChunk000Sub001Block061Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part019] using hcert

def TailChunk000Sub001Block061Part020SupportExplicit : Finset ℕ :=
  ([10814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part020 : ℚ :=
  (456807015625 : ℚ) / 533913660896713362

def SurrogateDiagonalTailChunk000Sub001Block061Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10814
    = surrogateDiagTailX0RatChunk000Sub001Block061Part020

theorem surrogateDiagonalTailChunk000Sub001Block061Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part020] using hcert

def TailChunk000Sub001Block061Part021SupportExplicit : Finset ℕ :=
  ([10815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part021 : ℚ :=
  (73005299525 : ℚ) / 84516902898499584

def SurrogateDiagonalTailChunk000Sub001Block061Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10815
    = surrogateDiagTailX0RatChunk000Sub001Block061Part021

theorem surrogateDiagonalTailChunk000Sub001Block061Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part021] using hcert

def TailChunk000Sub001Block061Part022SupportExplicit : Finset ℕ :=
  ([10817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part022 : ℚ :=
  (5037412375 : ℚ) / 1226364307172831232

def SurrogateDiagonalTailChunk000Sub001Block061Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10817
    = surrogateDiagTailX0RatChunk000Sub001Block061Part022

theorem surrogateDiagonalTailChunk000Sub001Block061Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part022] using hcert

def TailChunk000Sub001Block061Part023SupportExplicit : Finset ℕ :=
  ([10819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part023 : ℚ :=
  (158689307 : ℚ) / 40972347454924800

def SurrogateDiagonalTailChunk000Sub001Block061Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10819
    = surrogateDiagTailX0RatChunk000Sub001Block061Part023

theorem surrogateDiagonalTailChunk000Sub001Block061Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part023] using hcert

def TailChunk000Sub001Block061Part024SupportExplicit : Finset ℕ :=
  ([10821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block061Part024 : ℚ :=
  (812852091725 : ℚ) / 3382359266019806784

def SurrogateDiagonalTailChunk000Sub001Block061Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10821
    = surrogateDiagTailX0RatChunk000Sub001Block061Part024

theorem surrogateDiagonalTailChunk000Sub001Block061Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block061Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block061Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block061Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block061Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block061Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block061HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block061Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block061Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block061Part000
    + surrogateDiagTailX0RatChunk000Sub001Block061Part001
    + surrogateDiagTailX0RatChunk000Sub001Block061Part002
    + surrogateDiagTailX0RatChunk000Sub001Block061Part003
    + surrogateDiagTailX0RatChunk000Sub001Block061Part004
    + surrogateDiagTailX0RatChunk000Sub001Block061Part005
    + surrogateDiagTailX0RatChunk000Sub001Block061Part006
    + surrogateDiagTailX0RatChunk000Sub001Block061Part007
    + surrogateDiagTailX0RatChunk000Sub001Block061Part008
    + surrogateDiagTailX0RatChunk000Sub001Block061Part009

def surrogateDiagonalTailChunk000Sub001Block061MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block061Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block061Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block061Part010
    + surrogateDiagTailX0RatChunk000Sub001Block061Part011
    + surrogateDiagTailX0RatChunk000Sub001Block061Part012
    + surrogateDiagTailX0RatChunk000Sub001Block061Part013
    + surrogateDiagTailX0RatChunk000Sub001Block061Part014
    + surrogateDiagTailX0RatChunk000Sub001Block061Part015
    + surrogateDiagTailX0RatChunk000Sub001Block061Part016
    + surrogateDiagTailX0RatChunk000Sub001Block061Part017
    + surrogateDiagTailX0RatChunk000Sub001Block061Part018
    + surrogateDiagTailX0RatChunk000Sub001Block061Part019

def surrogateDiagonalTailChunk000Sub001Block061TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block061Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block061Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block061Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block061Part020
    + surrogateDiagTailX0RatChunk000Sub001Block061Part021
    + surrogateDiagTailX0RatChunk000Sub001Block061Part022
    + surrogateDiagTailX0RatChunk000Sub001Block061Part023
    + surrogateDiagTailX0RatChunk000Sub001Block061Part024

def surrogateDiagonalTailChunk000Sub001Block061Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block061HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block061MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block061TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block061 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block061Part000
    + surrogateDiagTailX0RatChunk000Sub001Block061Part001
    + surrogateDiagTailX0RatChunk000Sub001Block061Part002
    + surrogateDiagTailX0RatChunk000Sub001Block061Part003
    + surrogateDiagTailX0RatChunk000Sub001Block061Part004
    + surrogateDiagTailX0RatChunk000Sub001Block061Part005
    + surrogateDiagTailX0RatChunk000Sub001Block061Part006
    + surrogateDiagTailX0RatChunk000Sub001Block061Part007
    + surrogateDiagTailX0RatChunk000Sub001Block061Part008
    + surrogateDiagTailX0RatChunk000Sub001Block061Part009
    + surrogateDiagTailX0RatChunk000Sub001Block061Part010
    + surrogateDiagTailX0RatChunk000Sub001Block061Part011
    + surrogateDiagTailX0RatChunk000Sub001Block061Part012
    + surrogateDiagTailX0RatChunk000Sub001Block061Part013
    + surrogateDiagTailX0RatChunk000Sub001Block061Part014
    + surrogateDiagTailX0RatChunk000Sub001Block061Part015
    + surrogateDiagTailX0RatChunk000Sub001Block061Part016
    + surrogateDiagTailX0RatChunk000Sub001Block061Part017
    + surrogateDiagTailX0RatChunk000Sub001Block061Part018
    + surrogateDiagTailX0RatChunk000Sub001Block061Part019
    + surrogateDiagTailX0RatChunk000Sub001Block061Part020
    + surrogateDiagTailX0RatChunk000Sub001Block061Part021
    + surrogateDiagTailX0RatChunk000Sub001Block061Part022
    + surrogateDiagTailX0RatChunk000Sub001Block061Part023
    + surrogateDiagTailX0RatChunk000Sub001Block061Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block061_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block061Head + surrogateDiagTailX0RatChunk000Sub001Block061Mid + surrogateDiagTailX0RatChunk000Sub001Block061Tail =
      surrogateDiagTailX0RatChunk000Sub001Block061 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block061Head surrogateDiagTailX0RatChunk000Sub001Block061Mid surrogateDiagTailX0RatChunk000Sub001Block061Tail surrogateDiagTailX0RatChunk000Sub001Block061
  ring

def SurrogateDiagonalTailChunk000Sub001Block061HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block061HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block061Head

def SurrogateDiagonalTailChunk000Sub001Block061MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block061MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block061Mid

def SurrogateDiagonalTailChunk000Sub001Block061TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block061TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block061Tail

theorem surrogateDiagonalTailChunk000Sub001Block061_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block061HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block061MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block061TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block061Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block061 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block061HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block061MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block061TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block061Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block061_eq_head_add_mid_add_tail

/-- Block 062 covers tail-support indices [6550,6575) and q from 10822 to 10865. -/

def TailChunk000Sub001Block062Part000SupportExplicit : Finset ℕ :=
  ([10822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part000 : ℚ :=
  (87035726575 : ℚ) / 63948234175497216

def SurrogateDiagonalTailChunk000Sub001Block062Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10822
    = surrogateDiagTailX0RatChunk000Sub001Block062Part000

theorem surrogateDiagonalTailChunk000Sub001Block062Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part000] using hcert

def TailChunk000Sub001Block062Part001SupportExplicit : Finset ℕ :=
  ([10823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part001 : ℚ :=
  (8341164875 : ℚ) / 3957955582815277056

def SurrogateDiagonalTailChunk000Sub001Block062Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10823
    = surrogateDiagTailX0RatChunk000Sub001Block062Part001

theorem surrogateDiagonalTailChunk000Sub001Block062Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part001] using hcert

def TailChunk000Sub001Block062Part002SupportExplicit : Finset ℕ :=
  ([10826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part002 : ℚ :=
  (457821390625 : ℚ) / 536287925878908192

def SurrogateDiagonalTailChunk000Sub001Block062Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10826
    = surrogateDiagTailX0RatChunk000Sub001Block062Part002

theorem surrogateDiagonalTailChunk000Sub001Block062Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part002] using hcert

def TailChunk000Sub001Block062Part003SupportExplicit : Finset ℕ :=
  ([10831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10831
    = surrogateDiagTailX0RatChunk000Sub001Block062Part003

theorem surrogateDiagonalTailChunk000Sub001Block062Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part003] using hcert

def TailChunk000Sub001Block062Part004SupportExplicit : Finset ℕ :=
  ([10833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part004 : ℚ :=
  (211791045925 : ℚ) / 1387637305300426752

def SurrogateDiagonalTailChunk000Sub001Block062Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10833
    = surrogateDiagTailX0RatChunk000Sub001Block062Part004

theorem surrogateDiagonalTailChunk000Sub001Block062Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part004] using hcert

def TailChunk000Sub001Block062Part005SupportExplicit : Finset ℕ :=
  ([10834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part005 : ℚ :=
  (458498265625 : ℚ) / 537875162458747392

def SurrogateDiagonalTailChunk000Sub001Block062Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10834
    = surrogateDiagTailX0RatChunk000Sub001Block062Part005

theorem surrogateDiagonalTailChunk000Sub001Block062Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part005] using hcert

def TailChunk000Sub001Block062Part006SupportExplicit : Finset ℕ :=
  ([10835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part006 : ℚ :=
  (5516285353 : ℚ) / 53982508390809600

def SurrogateDiagonalTailChunk000Sub001Block062Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10835
    = surrogateDiagTailX0RatChunk000Sub001Block062Part006

theorem surrogateDiagonalTailChunk000Sub001Block062Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part006] using hcert

def TailChunk000Sub001Block062Part007SupportExplicit : Finset ℕ :=
  ([10837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10837
    = surrogateDiagTailX0RatChunk000Sub001Block062Part007

theorem surrogateDiagonalTailChunk000Sub001Block062Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part007] using hcert

def TailChunk000Sub001Block062Part008SupportExplicit : Finset ℕ :=
  ([10838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part008 : ℚ :=
  (458836890625 : ℚ) / 538670100675249522

def SurrogateDiagonalTailChunk000Sub001Block062Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10838
    = surrogateDiagTailX0RatChunk000Sub001Block062Part008

theorem surrogateDiagonalTailChunk000Sub001Block062Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part008] using hcert

def TailChunk000Sub001Block062Part009SupportExplicit : Finset ℕ :=
  ([10839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part009 : ℚ :=
  (7286018725 : ℚ) / 60802268859287424

def SurrogateDiagonalTailChunk000Sub001Block062Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10839
    = surrogateDiagTailX0RatChunk000Sub001Block062Part009

theorem surrogateDiagonalTailChunk000Sub001Block062Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part009] using hcert

def TailChunk000Sub001Block062Part010SupportExplicit : Finset ℕ :=
  ([10841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part010 : ℚ :=
  (25385511475 : ℚ) / 7633228733351534592

def SurrogateDiagonalTailChunk000Sub001Block062Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10841
    = surrogateDiagTailX0RatChunk000Sub001Block062Part010

theorem surrogateDiagonalTailChunk000Sub001Block062Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part010] using hcert

def TailChunk000Sub001Block062Part011SupportExplicit : Finset ℕ :=
  ([10842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part011 : ℚ :=
  (1114595309875 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub001Block062Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10842
    = surrogateDiagTailX0RatChunk000Sub001Block062Part011

theorem surrogateDiagonalTailChunk000Sub001Block062Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part011] using hcert

def TailChunk000Sub001Block062Part012SupportExplicit : Finset ℕ :=
  ([10843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part012 : ℚ :=
  (600590961925 : ℚ) / 18608685060561389568

def SurrogateDiagonalTailChunk000Sub001Block062Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10843
    = surrogateDiagTailX0RatChunk000Sub001Block062Part012

theorem surrogateDiagonalTailChunk000Sub001Block062Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part012] using hcert

def TailChunk000Sub001Block062Part013SupportExplicit : Finset ℕ :=
  ([10846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part013 : ℚ :=
  (9979096347 : ℚ) / 6715025339187200

def SurrogateDiagonalTailChunk000Sub001Block062Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10846
    = surrogateDiagTailX0RatChunk000Sub001Block062Part013

theorem surrogateDiagonalTailChunk000Sub001Block062Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part013] using hcert

def TailChunk000Sub001Block062Part014SupportExplicit : Finset ℕ :=
  ([10847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10847
    = surrogateDiagTailX0RatChunk000Sub001Block062Part014

theorem surrogateDiagonalTailChunk000Sub001Block062Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part014] using hcert

def TailChunk000Sub001Block062Part015SupportExplicit : Finset ℕ :=
  ([10849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part015 : ℚ :=
  (58776761 : ℚ) / 8658971768189025

def SurrogateDiagonalTailChunk000Sub001Block062Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10849
    = surrogateDiagTailX0RatChunk000Sub001Block062Part015

theorem surrogateDiagonalTailChunk000Sub001Block062Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part015] using hcert

def TailChunk000Sub001Block062Part016SupportExplicit : Finset ℕ :=
  ([10851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part016 : ℚ :=
  (204460274275 : ℚ) / 1710017431178575872

def SurrogateDiagonalTailChunk000Sub001Block062Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10851
    = surrogateDiagTailX0RatChunk000Sub001Block062Part016

theorem surrogateDiagonalTailChunk000Sub001Block062Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part016] using hcert

def TailChunk000Sub001Block062Part017SupportExplicit : Finset ℕ :=
  ([10853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10853
    = surrogateDiagTailX0RatChunk000Sub001Block062Part017

theorem surrogateDiagonalTailChunk000Sub001Block062Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part017] using hcert

def TailChunk000Sub001Block062Part018SupportExplicit : Finset ℕ :=
  ([10855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part018 : ℚ :=
  (712389499825 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk000Sub001Block062Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10855
    = surrogateDiagTailX0RatChunk000Sub001Block062Part018

theorem surrogateDiagonalTailChunk000Sub001Block062Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part018] using hcert

def TailChunk000Sub001Block062Part019SupportExplicit : Finset ℕ :=
  ([10857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part019 : ℚ :=
  (1330425383 : ℚ) / 3439373945241600

def SurrogateDiagonalTailChunk000Sub001Block062Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10857
    = surrogateDiagTailX0RatChunk000Sub001Block062Part019

theorem surrogateDiagonalTailChunk000Sub001Block062Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part019] using hcert

def TailChunk000Sub001Block062Part020SupportExplicit : Finset ℕ :=
  ([10858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part020 : ℚ :=
  (71535558751 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub001Block062Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10858
    = surrogateDiagTailX0RatChunk000Sub001Block062Part020

theorem surrogateDiagonalTailChunk000Sub001Block062Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part020] using hcert

def TailChunk000Sub001Block062Part021SupportExplicit : Finset ℕ :=
  ([10859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10859
    = surrogateDiagTailX0RatChunk000Sub001Block062Part021

theorem surrogateDiagonalTailChunk000Sub001Block062Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part021] using hcert

def TailChunk000Sub001Block062Part022SupportExplicit : Finset ℕ :=
  ([10861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10861
    = surrogateDiagTailX0RatChunk000Sub001Block062Part022

theorem surrogateDiagonalTailChunk000Sub001Block062Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part022] using hcert

def TailChunk000Sub001Block062Part023SupportExplicit : Finset ℕ :=
  ([10862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block062Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10862
    = surrogateDiagTailX0RatChunk000Sub001Block062Part023

theorem surrogateDiagonalTailChunk000Sub001Block062Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part023] using hcert

def TailChunk000Sub001Block062Part024SupportExplicit : Finset ℕ :=
  ([10865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block062Part024 : ℚ :=
  (4358554539 : ℚ) / 79878316831539200

def SurrogateDiagonalTailChunk000Sub001Block062Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10865
    = surrogateDiagTailX0RatChunk000Sub001Block062Part024

theorem surrogateDiagonalTailChunk000Sub001Block062Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block062Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block062Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block062Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block062Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block062Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block062HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block062Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block062Part000
    + surrogateDiagTailX0RatChunk000Sub001Block062Part001
    + surrogateDiagTailX0RatChunk000Sub001Block062Part002
    + surrogateDiagTailX0RatChunk000Sub001Block062Part003
    + surrogateDiagTailX0RatChunk000Sub001Block062Part004
    + surrogateDiagTailX0RatChunk000Sub001Block062Part005
    + surrogateDiagTailX0RatChunk000Sub001Block062Part006
    + surrogateDiagTailX0RatChunk000Sub001Block062Part007
    + surrogateDiagTailX0RatChunk000Sub001Block062Part008
    + surrogateDiagTailX0RatChunk000Sub001Block062Part009

def surrogateDiagonalTailChunk000Sub001Block062MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block062Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block062Part010
    + surrogateDiagTailX0RatChunk000Sub001Block062Part011
    + surrogateDiagTailX0RatChunk000Sub001Block062Part012
    + surrogateDiagTailX0RatChunk000Sub001Block062Part013
    + surrogateDiagTailX0RatChunk000Sub001Block062Part014
    + surrogateDiagTailX0RatChunk000Sub001Block062Part015
    + surrogateDiagTailX0RatChunk000Sub001Block062Part016
    + surrogateDiagTailX0RatChunk000Sub001Block062Part017
    + surrogateDiagTailX0RatChunk000Sub001Block062Part018
    + surrogateDiagTailX0RatChunk000Sub001Block062Part019

def surrogateDiagonalTailChunk000Sub001Block062TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block062Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block062Part020
    + surrogateDiagTailX0RatChunk000Sub001Block062Part021
    + surrogateDiagTailX0RatChunk000Sub001Block062Part022
    + surrogateDiagTailX0RatChunk000Sub001Block062Part023
    + surrogateDiagTailX0RatChunk000Sub001Block062Part024

def surrogateDiagonalTailChunk000Sub001Block062Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block062HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block062MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block062TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block062 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block062Part000
    + surrogateDiagTailX0RatChunk000Sub001Block062Part001
    + surrogateDiagTailX0RatChunk000Sub001Block062Part002
    + surrogateDiagTailX0RatChunk000Sub001Block062Part003
    + surrogateDiagTailX0RatChunk000Sub001Block062Part004
    + surrogateDiagTailX0RatChunk000Sub001Block062Part005
    + surrogateDiagTailX0RatChunk000Sub001Block062Part006
    + surrogateDiagTailX0RatChunk000Sub001Block062Part007
    + surrogateDiagTailX0RatChunk000Sub001Block062Part008
    + surrogateDiagTailX0RatChunk000Sub001Block062Part009
    + surrogateDiagTailX0RatChunk000Sub001Block062Part010
    + surrogateDiagTailX0RatChunk000Sub001Block062Part011
    + surrogateDiagTailX0RatChunk000Sub001Block062Part012
    + surrogateDiagTailX0RatChunk000Sub001Block062Part013
    + surrogateDiagTailX0RatChunk000Sub001Block062Part014
    + surrogateDiagTailX0RatChunk000Sub001Block062Part015
    + surrogateDiagTailX0RatChunk000Sub001Block062Part016
    + surrogateDiagTailX0RatChunk000Sub001Block062Part017
    + surrogateDiagTailX0RatChunk000Sub001Block062Part018
    + surrogateDiagTailX0RatChunk000Sub001Block062Part019
    + surrogateDiagTailX0RatChunk000Sub001Block062Part020
    + surrogateDiagTailX0RatChunk000Sub001Block062Part021
    + surrogateDiagTailX0RatChunk000Sub001Block062Part022
    + surrogateDiagTailX0RatChunk000Sub001Block062Part023
    + surrogateDiagTailX0RatChunk000Sub001Block062Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block062_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block062Head + surrogateDiagTailX0RatChunk000Sub001Block062Mid + surrogateDiagTailX0RatChunk000Sub001Block062Tail =
      surrogateDiagTailX0RatChunk000Sub001Block062 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block062Head surrogateDiagTailX0RatChunk000Sub001Block062Mid surrogateDiagTailX0RatChunk000Sub001Block062Tail surrogateDiagTailX0RatChunk000Sub001Block062
  ring

def SurrogateDiagonalTailChunk000Sub001Block062HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block062HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block062Head

def SurrogateDiagonalTailChunk000Sub001Block062MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block062MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block062Mid

def SurrogateDiagonalTailChunk000Sub001Block062TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block062TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block062Tail

theorem surrogateDiagonalTailChunk000Sub001Block062_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block062HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block062MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block062TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block062Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block062 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block062HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block062MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block062TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block062Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block062_eq_head_add_mid_add_tail

/-- Block 063 covers tail-support indices [6575,6600) and q from 10866 to 10905. -/

def TailChunk000Sub001Block063Part000SupportExplicit : Finset ℕ :=
  ([10866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part000 : ℚ :=
  (8201110829 : ℚ) / 8587982220993600

def SurrogateDiagonalTailChunk000Sub001Block063Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10866
    = surrogateDiagTailX0RatChunk000Sub001Block063Part000

theorem surrogateDiagonalTailChunk000Sub001Block063Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part000] using hcert

def TailChunk000Sub001Block063Part001SupportExplicit : Finset ℕ :=
  ([10867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block063Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10867
    = surrogateDiagTailX0RatChunk000Sub001Block063Part001

theorem surrogateDiagonalTailChunk000Sub001Block063Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part001] using hcert

def TailChunk000Sub001Block063Part002SupportExplicit : Finset ℕ :=
  ([10869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part002 : ℚ :=
  (410277673475 : ℚ) / 3442790768578741824

def SurrogateDiagonalTailChunk000Sub001Block063Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10869
    = surrogateDiagTailX0RatChunk000Sub001Block063Part002

theorem surrogateDiagonalTailChunk000Sub001Block063Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part002] using hcert

def TailChunk000Sub001Block063Part003SupportExplicit : Finset ℕ :=
  ([10870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part003 : ℚ :=
  (737894924375 : ℚ) / 445200998336308224

def SurrogateDiagonalTailChunk000Sub001Block063Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10870
    = surrogateDiagTailX0RatChunk000Sub001Block063Part003

theorem surrogateDiagonalTailChunk000Sub001Block063Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part003] using hcert

def TailChunk000Sub001Block063Part004SupportExplicit : Finset ℕ :=
  ([10871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part004 : ℚ :=
  (326332829975 : ℚ) / 1044542759509426176

def SurrogateDiagonalTailChunk000Sub001Block063Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10871
    = surrogateDiagTailX0RatChunk000Sub001Block063Part004

theorem surrogateDiagonalTailChunk000Sub001Block063Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part004] using hcert

def TailChunk000Sub001Block063Part005SupportExplicit : Finset ℕ :=
  ([10873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part005 : ℚ :=
  (23891344311 : ℚ) / 107630268310645600

def SurrogateDiagonalTailChunk000Sub001Block063Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10873
    = surrogateDiagTailX0RatChunk000Sub001Block063Part005

theorem surrogateDiagonalTailChunk000Sub001Block063Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part005] using hcert

def TailChunk000Sub001Block063Part006SupportExplicit : Finset ℕ :=
  ([10874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part006 : ℚ :=
  (461890140625 : ℚ) / 545864259527461152

def SurrogateDiagonalTailChunk000Sub001Block063Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10874
    = surrogateDiagTailX0RatChunk000Sub001Block063Part006

theorem surrogateDiagonalTailChunk000Sub001Block063Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part006] using hcert

def TailChunk000Sub001Block063Part007SupportExplicit : Finset ℕ :=
  ([10877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part007 : ℚ :=
  (3582546289325 : ℚ) / 16120321926842548224

def SurrogateDiagonalTailChunk000Sub001Block063Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10877
    = surrogateDiagTailX0RatChunk000Sub001Block063Part007

theorem surrogateDiagonalTailChunk000Sub001Block063Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part007] using hcert

def TailChunk000Sub001Block063Part008SupportExplicit : Finset ℕ :=
  ([10879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part008 : ℚ :=
  (229081411477 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk000Sub001Block063Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10879
    = surrogateDiagTailX0RatChunk000Sub001Block063Part008

theorem surrogateDiagonalTailChunk000Sub001Block063Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part008] using hcert

def TailChunk000Sub001Block063Part009SupportExplicit : Finset ℕ :=
  ([10882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part009 : ℚ :=
  (740112025 : ℚ) / 875956317192192

def SurrogateDiagonalTailChunk000Sub001Block063Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10882
    = surrogateDiagTailX0RatChunk000Sub001Block063Part009

theorem surrogateDiagonalTailChunk000Sub001Block063Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part009] using hcert

def TailChunk000Sub001Block063Part010SupportExplicit : Finset ℕ :=
  ([10883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part010 : ℚ :=
  (1850620140625 : ℚ) / 8766005803384168722

def SurrogateDiagonalTailChunk000Sub001Block063Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10883
    = surrogateDiagTailX0RatChunk000Sub001Block063Part010

theorem surrogateDiagonalTailChunk000Sub001Block063Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part010] using hcert

def TailChunk000Sub001Block063Part011SupportExplicit : Finset ℕ :=
  ([10885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part011 : ℚ :=
  (39477689263 : ℚ) / 76615845929164800

def SurrogateDiagonalTailChunk000Sub001Block063Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10885
    = surrogateDiagTailX0RatChunk000Sub001Block063Part011

theorem surrogateDiagonalTailChunk000Sub001Block063Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part011] using hcert

def TailChunk000Sub001Block063Part012SupportExplicit : Finset ℕ :=
  ([10886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part012 : ℚ :=
  (462910140625 : ℚ) / 548278249255916562

def SurrogateDiagonalTailChunk000Sub001Block063Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10886
    = surrogateDiagTailX0RatChunk000Sub001Block063Part012

theorem surrogateDiagonalTailChunk000Sub001Block063Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part012] using hcert

def TailChunk000Sub001Block063Part013SupportExplicit : Finset ℕ :=
  ([10887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part013 : ℚ :=
  (151007739397 : ℚ) / 218933014583347200

def SurrogateDiagonalTailChunk000Sub001Block063Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10887
    = surrogateDiagTailX0RatChunk000Sub001Block063Part013

theorem surrogateDiagonalTailChunk000Sub001Block063Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part013] using hcert

def TailChunk000Sub001Block063Part014SupportExplicit : Finset ℕ :=
  ([10889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part014 : ℚ :=
  (1852661265625 : ℚ) / 8785355022485524992

def SurrogateDiagonalTailChunk000Sub001Block063Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10889
    = surrogateDiagTailX0RatChunk000Sub001Block063Part014

theorem surrogateDiagonalTailChunk000Sub001Block063Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part014] using hcert

def TailChunk000Sub001Block063Part015SupportExplicit : Finset ℕ :=
  ([10891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part015 : ℚ :=
  (2965347025 : ℚ) / 14066898999646482

def SurrogateDiagonalTailChunk000Sub001Block063Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10891
    = surrogateDiagTailX0RatChunk000Sub001Block063Part015

theorem surrogateDiagonalTailChunk000Sub001Block063Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part015] using hcert

def TailChunk000Sub001Block063Part016SupportExplicit : Finset ℕ :=
  ([10893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part016 : ℚ :=
  (41190649417 : ℚ) / 69466167899488800

def SurrogateDiagonalTailChunk000Sub001Block063Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10893
    = surrogateDiagTailX0RatChunk000Sub001Block063Part016

theorem surrogateDiagonalTailChunk000Sub001Block063Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part016] using hcert

def TailChunk000Sub001Block063Part017SupportExplicit : Finset ℕ :=
  ([10894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part017 : ℚ :=
  (19280905525 : ℚ) / 17987644593236736

def SurrogateDiagonalTailChunk000Sub001Block063Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10894
    = surrogateDiagTailX0RatChunk000Sub001Block063Part017

theorem surrogateDiagonalTailChunk000Sub001Block063Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part017] using hcert

def TailChunk000Sub001Block063Part018SupportExplicit : Finset ℕ :=
  ([10895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part018 : ℚ :=
  (5041888969225 : ℚ) / 14404504575637997568

def SurrogateDiagonalTailChunk000Sub001Block063Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10895
    = surrogateDiagTailX0RatChunk000Sub001Block063Part018

theorem surrogateDiagonalTailChunk000Sub001Block063Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part018] using hcert

def TailChunk000Sub001Block063Part019SupportExplicit : Finset ℕ :=
  ([10897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part019 : ℚ :=
  (26852040667 : ℚ) / 109973153010155520

def SurrogateDiagonalTailChunk000Sub001Block063Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10897
    = surrogateDiagTailX0RatChunk000Sub001Block063Part019

theorem surrogateDiagonalTailChunk000Sub001Block063Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part019] using hcert

def TailChunk000Sub001Block063Part020SupportExplicit : Finset ℕ :=
  ([10898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part020 : ℚ :=
  (463931265625 : ℚ) / 550700236733501952

def SurrogateDiagonalTailChunk000Sub001Block063Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10898
    = surrogateDiagTailX0RatChunk000Sub001Block063Part020

theorem surrogateDiagonalTailChunk000Sub001Block063Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part020] using hcert

def TailChunk000Sub001Block063Part021SupportExplicit : Finset ℕ :=
  ([10901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part021 : ℚ :=
  (254984191489 : ℚ) / 960788129202000000

def SurrogateDiagonalTailChunk000Sub001Block063Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10901
    = surrogateDiagTailX0RatChunk000Sub001Block063Part021

theorem surrogateDiagonalTailChunk000Sub001Block063Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part021] using hcert

def TailChunk000Sub001Block063Part022SupportExplicit : Finset ℕ :=
  ([10902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part022 : ℚ :=
  (489953190275 : ℚ) / 173454663162553344

def SurrogateDiagonalTailChunk000Sub001Block063Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10902
    = surrogateDiagTailX0RatChunk000Sub001Block063Part022

theorem surrogateDiagonalTailChunk000Sub001Block063Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part022] using hcert

def TailChunk000Sub001Block063Part023SupportExplicit : Finset ℕ :=
  ([10903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part023 : ℚ :=
  (1857428265625 : ℚ) / 8830627762265983602

def SurrogateDiagonalTailChunk000Sub001Block063Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10903
    = surrogateDiagTailX0RatChunk000Sub001Block063Part023

theorem surrogateDiagonalTailChunk000Sub001Block063Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part023] using hcert

def TailChunk000Sub001Block063Part024SupportExplicit : Finset ℕ :=
  ([10905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block063Part024 : ℚ :=
  (401159977975 : ℚ) / 474222372860510208

def SurrogateDiagonalTailChunk000Sub001Block063Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10905
    = surrogateDiagTailX0RatChunk000Sub001Block063Part024

theorem surrogateDiagonalTailChunk000Sub001Block063Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block063Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block063Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block063Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block063Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block063Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block063HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block063Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block063Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block063Part000
    + surrogateDiagTailX0RatChunk000Sub001Block063Part001
    + surrogateDiagTailX0RatChunk000Sub001Block063Part002
    + surrogateDiagTailX0RatChunk000Sub001Block063Part003
    + surrogateDiagTailX0RatChunk000Sub001Block063Part004
    + surrogateDiagTailX0RatChunk000Sub001Block063Part005
    + surrogateDiagTailX0RatChunk000Sub001Block063Part006
    + surrogateDiagTailX0RatChunk000Sub001Block063Part007
    + surrogateDiagTailX0RatChunk000Sub001Block063Part008
    + surrogateDiagTailX0RatChunk000Sub001Block063Part009

def surrogateDiagonalTailChunk000Sub001Block063MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block063Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block063Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block063Part010
    + surrogateDiagTailX0RatChunk000Sub001Block063Part011
    + surrogateDiagTailX0RatChunk000Sub001Block063Part012
    + surrogateDiagTailX0RatChunk000Sub001Block063Part013
    + surrogateDiagTailX0RatChunk000Sub001Block063Part014
    + surrogateDiagTailX0RatChunk000Sub001Block063Part015
    + surrogateDiagTailX0RatChunk000Sub001Block063Part016
    + surrogateDiagTailX0RatChunk000Sub001Block063Part017
    + surrogateDiagTailX0RatChunk000Sub001Block063Part018
    + surrogateDiagTailX0RatChunk000Sub001Block063Part019

def surrogateDiagonalTailChunk000Sub001Block063TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block063Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block063Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block063Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block063Part020
    + surrogateDiagTailX0RatChunk000Sub001Block063Part021
    + surrogateDiagTailX0RatChunk000Sub001Block063Part022
    + surrogateDiagTailX0RatChunk000Sub001Block063Part023
    + surrogateDiagTailX0RatChunk000Sub001Block063Part024

def surrogateDiagonalTailChunk000Sub001Block063Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block063HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block063MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block063TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block063 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block063Part000
    + surrogateDiagTailX0RatChunk000Sub001Block063Part001
    + surrogateDiagTailX0RatChunk000Sub001Block063Part002
    + surrogateDiagTailX0RatChunk000Sub001Block063Part003
    + surrogateDiagTailX0RatChunk000Sub001Block063Part004
    + surrogateDiagTailX0RatChunk000Sub001Block063Part005
    + surrogateDiagTailX0RatChunk000Sub001Block063Part006
    + surrogateDiagTailX0RatChunk000Sub001Block063Part007
    + surrogateDiagTailX0RatChunk000Sub001Block063Part008
    + surrogateDiagTailX0RatChunk000Sub001Block063Part009
    + surrogateDiagTailX0RatChunk000Sub001Block063Part010
    + surrogateDiagTailX0RatChunk000Sub001Block063Part011
    + surrogateDiagTailX0RatChunk000Sub001Block063Part012
    + surrogateDiagTailX0RatChunk000Sub001Block063Part013
    + surrogateDiagTailX0RatChunk000Sub001Block063Part014
    + surrogateDiagTailX0RatChunk000Sub001Block063Part015
    + surrogateDiagTailX0RatChunk000Sub001Block063Part016
    + surrogateDiagTailX0RatChunk000Sub001Block063Part017
    + surrogateDiagTailX0RatChunk000Sub001Block063Part018
    + surrogateDiagTailX0RatChunk000Sub001Block063Part019
    + surrogateDiagTailX0RatChunk000Sub001Block063Part020
    + surrogateDiagTailX0RatChunk000Sub001Block063Part021
    + surrogateDiagTailX0RatChunk000Sub001Block063Part022
    + surrogateDiagTailX0RatChunk000Sub001Block063Part023
    + surrogateDiagTailX0RatChunk000Sub001Block063Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block063_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block063Head + surrogateDiagTailX0RatChunk000Sub001Block063Mid + surrogateDiagTailX0RatChunk000Sub001Block063Tail =
      surrogateDiagTailX0RatChunk000Sub001Block063 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block063Head surrogateDiagTailX0RatChunk000Sub001Block063Mid surrogateDiagTailX0RatChunk000Sub001Block063Tail surrogateDiagTailX0RatChunk000Sub001Block063
  ring

def SurrogateDiagonalTailChunk000Sub001Block063HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block063HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block063Head

def SurrogateDiagonalTailChunk000Sub001Block063MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block063MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block063Mid

def SurrogateDiagonalTailChunk000Sub001Block063TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block063TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block063Tail

theorem surrogateDiagonalTailChunk000Sub001Block063_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block063HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block063MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block063TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block063Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block063 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block063HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block063MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block063TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block063Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block063_eq_head_add_mid_add_tail

/-- Block 064 covers tail-support indices [6600,6625) and q from 10906 to 10946. -/

def TailChunk000Sub001Block064Part000SupportExplicit : Finset ℕ :=
  ([10906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part000 : ℚ :=
  (58441021663 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block064Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10906
    = surrogateDiagTailX0RatChunk000Sub001Block064Part000

theorem surrogateDiagonalTailChunk000Sub001Block064Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part000] using hcert

def TailChunk000Sub001Block064Part001SupportExplicit : Finset ℕ :=
  ([10907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part001 : ℚ :=
  (6544269551275 : ℚ) / 25569834530503477248

def SurrogateDiagonalTailChunk000Sub001Block064Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10907
    = surrogateDiagTailX0RatChunk000Sub001Block064Part001

theorem surrogateDiagonalTailChunk000Sub001Block064Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part001] using hcert

def TailChunk000Sub001Block064Part002SupportExplicit : Finset ℕ :=
  ([10909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part002 : ℚ :=
  (1859473140625 : ℚ) / 8850083833688730912

def SurrogateDiagonalTailChunk000Sub001Block064Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10909
    = surrogateDiagTailX0RatChunk000Sub001Block064Part002

theorem surrogateDiagonalTailChunk000Sub001Block064Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part002] using hcert

def TailChunk000Sub001Block064Part003SupportExplicit : Finset ℕ :=
  ([10910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part003 : ℚ :=
  (7061931083 : ℚ) / 4517964564230400

def SurrogateDiagonalTailChunk000Sub001Block064Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10910
    = surrogateDiagTailX0RatChunk000Sub001Block064Part003

theorem surrogateDiagonalTailChunk000Sub001Block064Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part003] using hcert

def TailChunk000Sub001Block064Part004SupportExplicit : Finset ℕ :=
  ([10911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part004 : ℚ :=
  (3305748636325 : ℚ) / 6992658831556528128

def SurrogateDiagonalTailChunk000Sub001Block064Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10911
    = surrogateDiagTailX0RatChunk000Sub001Block064Part004

theorem surrogateDiagonalTailChunk000Sub001Block064Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part004] using hcert

def TailChunk000Sub001Block064Part005SupportExplicit : Finset ℕ :=
  ([10913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part005 : ℚ :=
  (360470523175 : ℚ) / 1193388067557974088

def SurrogateDiagonalTailChunk000Sub001Block064Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10913
    = surrogateDiagTailX0RatChunk000Sub001Block064Part005

theorem surrogateDiagonalTailChunk000Sub001Block064Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part005] using hcert

def TailChunk000Sub001Block064Part006SupportExplicit : Finset ℕ :=
  ([10914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part006 : ℚ :=
  (8994383825 : ℚ) / 2586069924642816

def SurrogateDiagonalTailChunk000Sub001Block064Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10914
    = surrogateDiagTailX0RatChunk000Sub001Block064Part006

theorem surrogateDiagonalTailChunk000Sub001Block064Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part006] using hcert

def TailChunk000Sub001Block064Part007SupportExplicit : Finset ℕ :=
  ([10915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part007 : ℚ :=
  (2372055389825 : ℚ) / 6083574150107234304

def SurrogateDiagonalTailChunk000Sub001Block064Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10915
    = surrogateDiagTailX0RatChunk000Sub001Block064Part007

theorem surrogateDiagonalTailChunk000Sub001Block064Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part007] using hcert

def TailChunk000Sub001Block064Part008SupportExplicit : Finset ℕ :=
  ([10918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part008 : ℚ :=
  (1805385550975 : ℚ) / 1978977791407638528

def SurrogateDiagonalTailChunk000Sub001Block064Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10918
    = surrogateDiagTailX0RatChunk000Sub001Block064Part008

theorem surrogateDiagonalTailChunk000Sub001Block064Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part008] using hcert

def TailChunk000Sub001Block064Part009SupportExplicit : Finset ℕ :=
  ([10919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part009 : ℚ :=
  (144038033381 : ℚ) / 650641656998937600

def SurrogateDiagonalTailChunk000Sub001Block064Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10919
    = surrogateDiagTailX0RatChunk000Sub001Block064Part009

theorem surrogateDiagonalTailChunk000Sub001Block064Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part009] using hcert

def TailChunk000Sub001Block064Part010SupportExplicit : Finset ℕ :=
  ([10921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part010 : ℚ :=
  (25054184075 : ℚ) / 113467156482497796

def SurrogateDiagonalTailChunk000Sub001Block064Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10921
    = surrogateDiagTailX0RatChunk000Sub001Block064Part010

theorem surrogateDiagonalTailChunk000Sub001Block064Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part010] using hcert

def TailChunk000Sub001Block064Part011SupportExplicit : Finset ℕ :=
  ([10922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part011 : ℚ :=
  (1801483744225 : ℚ) / 1961129176680094848

def SurrogateDiagonalTailChunk000Sub001Block064Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10922
    = surrogateDiagTailX0RatChunk000Sub001Block064Part011

theorem surrogateDiagonalTailChunk000Sub001Block064Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part011] using hcert

def TailChunk000Sub001Block064Part012SupportExplicit : Finset ℕ :=
  ([10923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part012 : ℚ :=
  (58112362181 : ℚ) / 94892654736000000

def SurrogateDiagonalTailChunk000Sub001Block064Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10923
    = surrogateDiagTailX0RatChunk000Sub001Block064Part012

theorem surrogateDiagonalTailChunk000Sub001Block064Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part012] using hcert

def TailChunk000Sub001Block064Part013SupportExplicit : Finset ℕ :=
  ([10929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part013 : ℚ :=
  (3316665635725 : ℚ) / 7038929369128791168

def SurrogateDiagonalTailChunk000Sub001Block064Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10929
    = surrogateDiagTailX0RatChunk000Sub001Block064Part013

theorem surrogateDiagonalTailChunk000Sub001Block064Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part013] using hcert

def TailChunk000Sub001Block064Part014SupportExplicit : Finset ℕ :=
  ([10930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part014 : ℚ :=
  (746064057875 : ℚ) / 455121531319762944

def SurrogateDiagonalTailChunk000Sub001Block064Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10930
    = surrogateDiagTailX0RatChunk000Sub001Block064Part014

theorem surrogateDiagonalTailChunk000Sub001Block064Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part014] using hcert

def TailChunk000Sub001Block064Part015SupportExplicit : Finset ℕ :=
  ([10931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part015 : ℚ :=
  (1130144072375 : ℚ) / 4639761441548402688

def SurrogateDiagonalTailChunk000Sub001Block064Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10931
    = surrogateDiagTailX0RatChunk000Sub001Block064Part015

theorem surrogateDiagonalTailChunk000Sub001Block064Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part015] using hcert

def TailChunk000Sub001Block064Part016SupportExplicit : Finset ℕ :=
  ([10934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part016 : ℚ :=
  (55618023799 : ℚ) / 31123183392000000

def SurrogateDiagonalTailChunk000Sub001Block064Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10934
    = surrogateDiagTailX0RatChunk000Sub001Block064Part016

theorem surrogateDiagonalTailChunk000Sub001Block064Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part016] using hcert

def TailChunk000Sub001Block064Part017SupportExplicit : Finset ℕ :=
  ([10937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part017 : ℚ :=
  (1869030765625 : ℚ) / 8941304264798065152

def SurrogateDiagonalTailChunk000Sub001Block064Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10937
    = surrogateDiagTailX0RatChunk000Sub001Block064Part017

theorem surrogateDiagonalTailChunk000Sub001Block064Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part017] using hcert

def TailChunk000Sub001Block064Part018SupportExplicit : Finset ℕ :=
  ([10938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part018 : ℚ :=
  (124550625 : ℚ) / 44081207439424

def SurrogateDiagonalTailChunk000Sub001Block064Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10938
    = surrogateDiagTailX0RatChunk000Sub001Block064Part018

theorem surrogateDiagonalTailChunk000Sub001Block064Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part018] using hcert

def TailChunk000Sub001Block064Part019SupportExplicit : Finset ℕ :=
  ([10939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part019 : ℚ :=
  (1869714390625 : ℚ) / 8947846881749253042

def SurrogateDiagonalTailChunk000Sub001Block064Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10939
    = surrogateDiagTailX0RatChunk000Sub001Block064Part019

theorem surrogateDiagonalTailChunk000Sub001Block064Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part019] using hcert

def TailChunk000Sub001Block064Part020SupportExplicit : Finset ℕ :=
  ([10941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part020 : ℚ :=
  (2030813677 : ℚ) / 2808222076108800

def SurrogateDiagonalTailChunk000Sub001Block064Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10941
    = surrogateDiagTailX0RatChunk000Sub001Block064Part020

theorem surrogateDiagonalTailChunk000Sub001Block064Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part020] using hcert

def TailChunk000Sub001Block064Part021SupportExplicit : Finset ℕ :=
  ([10942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part021 : ℚ :=
  (748296025 : ℚ) / 895439308861362

def SurrogateDiagonalTailChunk000Sub001Block064Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10942
    = surrogateDiagTailX0RatChunk000Sub001Block064Part021

theorem surrogateDiagonalTailChunk000Sub001Block064Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part021] using hcert

def TailChunk000Sub001Block064Part022SupportExplicit : Finset ℕ :=
  ([10943] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part022 : ℚ :=
  (283221518029 : ℚ) / 1243777004155699200

def SurrogateDiagonalTailChunk000Sub001Block064Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10943
    = surrogateDiagTailX0RatChunk000Sub001Block064Part022

theorem surrogateDiagonalTailChunk000Sub001Block064Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part022] using hcert

def TailChunk000Sub001Block064Part023SupportExplicit : Finset ℕ :=
  ([10945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part023 : ℚ :=
  (43815330763 : ℚ) / 98384704430284800

def SurrogateDiagonalTailChunk000Sub001Block064Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10945
    = surrogateDiagTailX0RatChunk000Sub001Block064Part023

theorem surrogateDiagonalTailChunk000Sub001Block064Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part023] using hcert

def TailChunk000Sub001Block064Part024SupportExplicit : Finset ℕ :=
  ([10946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block064Part024 : ℚ :=
  (1268858639 : ℚ) / 1195130242252800

def SurrogateDiagonalTailChunk000Sub001Block064Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10946
    = surrogateDiagTailX0RatChunk000Sub001Block064Part024

theorem surrogateDiagonalTailChunk000Sub001Block064Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block064Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block064Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block064Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block064Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block064Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block064HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block064Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block064Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block064Part000
    + surrogateDiagTailX0RatChunk000Sub001Block064Part001
    + surrogateDiagTailX0RatChunk000Sub001Block064Part002
    + surrogateDiagTailX0RatChunk000Sub001Block064Part003
    + surrogateDiagTailX0RatChunk000Sub001Block064Part004
    + surrogateDiagTailX0RatChunk000Sub001Block064Part005
    + surrogateDiagTailX0RatChunk000Sub001Block064Part006
    + surrogateDiagTailX0RatChunk000Sub001Block064Part007
    + surrogateDiagTailX0RatChunk000Sub001Block064Part008
    + surrogateDiagTailX0RatChunk000Sub001Block064Part009

def surrogateDiagonalTailChunk000Sub001Block064MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block064Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block064Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block064Part010
    + surrogateDiagTailX0RatChunk000Sub001Block064Part011
    + surrogateDiagTailX0RatChunk000Sub001Block064Part012
    + surrogateDiagTailX0RatChunk000Sub001Block064Part013
    + surrogateDiagTailX0RatChunk000Sub001Block064Part014
    + surrogateDiagTailX0RatChunk000Sub001Block064Part015
    + surrogateDiagTailX0RatChunk000Sub001Block064Part016
    + surrogateDiagTailX0RatChunk000Sub001Block064Part017
    + surrogateDiagTailX0RatChunk000Sub001Block064Part018
    + surrogateDiagTailX0RatChunk000Sub001Block064Part019

def surrogateDiagonalTailChunk000Sub001Block064TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block064Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block064Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block064Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block064Part020
    + surrogateDiagTailX0RatChunk000Sub001Block064Part021
    + surrogateDiagTailX0RatChunk000Sub001Block064Part022
    + surrogateDiagTailX0RatChunk000Sub001Block064Part023
    + surrogateDiagTailX0RatChunk000Sub001Block064Part024

def surrogateDiagonalTailChunk000Sub001Block064Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block064HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block064MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block064TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block064 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block064Part000
    + surrogateDiagTailX0RatChunk000Sub001Block064Part001
    + surrogateDiagTailX0RatChunk000Sub001Block064Part002
    + surrogateDiagTailX0RatChunk000Sub001Block064Part003
    + surrogateDiagTailX0RatChunk000Sub001Block064Part004
    + surrogateDiagTailX0RatChunk000Sub001Block064Part005
    + surrogateDiagTailX0RatChunk000Sub001Block064Part006
    + surrogateDiagTailX0RatChunk000Sub001Block064Part007
    + surrogateDiagTailX0RatChunk000Sub001Block064Part008
    + surrogateDiagTailX0RatChunk000Sub001Block064Part009
    + surrogateDiagTailX0RatChunk000Sub001Block064Part010
    + surrogateDiagTailX0RatChunk000Sub001Block064Part011
    + surrogateDiagTailX0RatChunk000Sub001Block064Part012
    + surrogateDiagTailX0RatChunk000Sub001Block064Part013
    + surrogateDiagTailX0RatChunk000Sub001Block064Part014
    + surrogateDiagTailX0RatChunk000Sub001Block064Part015
    + surrogateDiagTailX0RatChunk000Sub001Block064Part016
    + surrogateDiagTailX0RatChunk000Sub001Block064Part017
    + surrogateDiagTailX0RatChunk000Sub001Block064Part018
    + surrogateDiagTailX0RatChunk000Sub001Block064Part019
    + surrogateDiagTailX0RatChunk000Sub001Block064Part020
    + surrogateDiagTailX0RatChunk000Sub001Block064Part021
    + surrogateDiagTailX0RatChunk000Sub001Block064Part022
    + surrogateDiagTailX0RatChunk000Sub001Block064Part023
    + surrogateDiagTailX0RatChunk000Sub001Block064Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block064_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block064Head + surrogateDiagTailX0RatChunk000Sub001Block064Mid + surrogateDiagTailX0RatChunk000Sub001Block064Tail =
      surrogateDiagTailX0RatChunk000Sub001Block064 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block064Head surrogateDiagTailX0RatChunk000Sub001Block064Mid surrogateDiagTailX0RatChunk000Sub001Block064Tail surrogateDiagTailX0RatChunk000Sub001Block064
  ring

def SurrogateDiagonalTailChunk000Sub001Block064HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block064HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block064Head

def SurrogateDiagonalTailChunk000Sub001Block064MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block064MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block064Mid

def SurrogateDiagonalTailChunk000Sub001Block064TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block064TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block064Tail

theorem surrogateDiagonalTailChunk000Sub001Block064_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block064HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block064MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block064TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block064Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block064 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block064HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block064MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block064TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block064Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block064_eq_head_add_mid_add_tail

/-- Block 065 covers tail-support indices [6625,6650) and q from 10947 to 10990. -/

def TailChunk000Sub001Block065Part000SupportExplicit : Finset ℕ :=
  ([10947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part000 : ℚ :=
  (8467192983 : ℚ) / 16378956433326080

def SurrogateDiagonalTailChunk000Sub001Block065Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10947
    = surrogateDiagTailX0RatChunk000Sub001Block065Part000

theorem surrogateDiagonalTailChunk000Sub001Block065Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part000] using hcert

def TailChunk000Sub001Block065Part001SupportExplicit : Finset ℕ :=
  ([10949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part001 : ℚ :=
  (1873134390625 : ℚ) / 8980613841465329952

def SurrogateDiagonalTailChunk000Sub001Block065Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10949
    = surrogateDiagTailX0RatChunk000Sub001Block065Part001

theorem surrogateDiagonalTailChunk000Sub001Block065Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part001] using hcert

def TailChunk000Sub001Block065Part002SupportExplicit : Finset ℕ :=
  ([10951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part002 : ℚ :=
  (2401357527525 : ℚ) / 10811572637175218176

def SurrogateDiagonalTailChunk000Sub001Block065Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10951
    = surrogateDiagTailX0RatChunk000Sub001Block065Part002

theorem surrogateDiagonalTailChunk000Sub001Block065Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part002] using hcert

def TailChunk000Sub001Block065Part003SupportExplicit : Finset ℕ :=
  ([10954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part003 : ℚ :=
  (468711390625 : ℚ) / 562109111969885472

def SurrogateDiagonalTailChunk000Sub001Block065Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10954
    = surrogateDiagTailX0RatChunk000Sub001Block065Part003

theorem surrogateDiagonalTailChunk000Sub001Block065Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part003] using hcert

def TailChunk000Sub001Block065Part004SupportExplicit : Finset ℕ :=
  ([10955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part004 : ℚ :=
  (124961736875 : ℚ) / 245663267217997824

def SurrogateDiagonalTailChunk000Sub001Block065Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10955
    = surrogateDiagTailX0RatChunk000Sub001Block065Part004

theorem surrogateDiagonalTailChunk000Sub001Block065Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part004] using hcert

def TailChunk000Sub001Block065Part005SupportExplicit : Finset ℕ :=
  ([10957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part005 : ℚ :=
  (1875872640625 : ℚ) / 9006892138006516512

def SurrogateDiagonalTailChunk000Sub001Block065Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10957
    = surrogateDiagTailX0RatChunk000Sub001Block065Part005

theorem surrogateDiagonalTailChunk000Sub001Block065Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part005] using hcert

def TailChunk000Sub001Block065Part006SupportExplicit : Finset ℕ :=
  ([10958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part006 : ℚ :=
  (469053765625 : ℚ) / 562930758625407282

def SurrogateDiagonalTailChunk000Sub001Block065Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10958
    = surrogateDiagTailX0RatChunk000Sub001Block065Part006

theorem surrogateDiagonalTailChunk000Sub001Block065Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part006] using hcert

def TailChunk000Sub001Block065Part007SupportExplicit : Finset ℕ :=
  ([10959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part007 : ℚ :=
  (49172274677 : ℚ) / 67989631559270400

def SurrogateDiagonalTailChunk000Sub001Block065Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10959
    = surrogateDiagTailX0RatChunk000Sub001Block065Part007

theorem surrogateDiagonalTailChunk000Sub001Block065Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part007] using hcert

def TailChunk000Sub001Block065Part008SupportExplicit : Finset ℕ :=
  ([10961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part008 : ℚ :=
  (65094242575 : ℚ) / 298377354500112384

def SurrogateDiagonalTailChunk000Sub001Block065Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10961
    = surrogateDiagTailX0RatChunk000Sub001Block065Part008

theorem surrogateDiagonalTailChunk000Sub001Block065Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part008] using hcert

def TailChunk000Sub001Block065Part009SupportExplicit : Finset ℕ :=
  ([10963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part009 : ℚ :=
  (6890914377175 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk000Sub001Block065Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10963
    = surrogateDiagTailX0RatChunk000Sub001Block065Part009

theorem surrogateDiagonalTailChunk000Sub001Block065Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part009] using hcert

def TailChunk000Sub001Block065Part010SupportExplicit : Finset ℕ :=
  ([10965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part010 : ℚ :=
  (2696187635875 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub001Block065Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10965
    = surrogateDiagTailX0RatChunk000Sub001Block065Part010

theorem surrogateDiagonalTailChunk000Sub001Block065Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part010] using hcert

def TailChunk000Sub001Block065Part011SupportExplicit : Finset ℕ :=
  ([10966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part011 : ℚ :=
  (469738890625 : ℚ) / 564576753897835122

def SurrogateDiagonalTailChunk000Sub001Block065Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10966
    = surrogateDiagTailX0RatChunk000Sub001Block065Part011

theorem surrogateDiagonalTailChunk000Sub001Block065Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part011] using hcert

def TailChunk000Sub001Block065Part012SupportExplicit : Finset ℕ :=
  ([10967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part012 : ℚ :=
  (258082756561 : ℚ) / 984292563404851200

def SurrogateDiagonalTailChunk000Sub001Block065Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10967
    = surrogateDiagTailX0RatChunk000Sub001Block065Part012

theorem surrogateDiagonalTailChunk000Sub001Block065Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part012] using hcert

def TailChunk000Sub001Block065Part013SupportExplicit : Finset ℕ :=
  ([10969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part013 : ℚ :=
  (364180702375 : ℚ) / 1218088684047044808

def SurrogateDiagonalTailChunk000Sub001Block065Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10969
    = surrogateDiagTailX0RatChunk000Sub001Block065Part013

theorem surrogateDiagonalTailChunk000Sub001Block065Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part013] using hcert

def TailChunk000Sub001Block065Part014SupportExplicit : Finset ℕ :=
  ([10970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part014 : ℚ :=
  (751535151875 : ℚ) / 461826708042153984

def SurrogateDiagonalTailChunk000Sub001Block065Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10970
    = surrogateDiagTailX0RatChunk000Sub001Block065Part014

theorem surrogateDiagonalTailChunk000Sub001Block065Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part014] using hcert

def TailChunk000Sub001Block065Part015SupportExplicit : Finset ℕ :=
  ([10973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part015 : ℚ :=
  (1881355140625 : ℚ) / 9059621698731500832

def SurrogateDiagonalTailChunk000Sub001Block065Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10973
    = surrogateDiagTailX0RatChunk000Sub001Block065Part015

theorem surrogateDiagonalTailChunk000Sub001Block065Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part015] using hcert

def TailChunk000Sub001Block065Part016SupportExplicit : Finset ℕ :=
  ([10974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part016 : ℚ :=
  (819941221 : ℚ) / 252915725030400

def SurrogateDiagonalTailChunk000Sub001Block065Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10974
    = surrogateDiagTailX0RatChunk000Sub001Block065Part016

theorem surrogateDiagonalTailChunk000Sub001Block065Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part016] using hcert

def TailChunk000Sub001Block065Part017SupportExplicit : Finset ℕ :=
  ([10977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part017 : ℚ :=
  (522855643025 : ℚ) / 895430038044049296

def SurrogateDiagonalTailChunk000Sub001Block065Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10977
    = surrogateDiagTailX0RatChunk000Sub001Block065Part017

theorem surrogateDiagonalTailChunk000Sub001Block065Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part017] using hcert

def TailChunk000Sub001Block065Part018SupportExplicit : Finset ℕ :=
  ([10978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part018 : ℚ :=
  (11286558529 : ℚ) / 10253047535467200

def SurrogateDiagonalTailChunk000Sub001Block065Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10978
    = surrogateDiagTailX0RatChunk000Sub001Block065Part018

theorem surrogateDiagonalTailChunk000Sub001Block065Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part018] using hcert

def TailChunk000Sub001Block065Part019SupportExplicit : Finset ℕ :=
  ([10979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block065Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10979
    = surrogateDiagTailX0RatChunk000Sub001Block065Part019

theorem surrogateDiagonalTailChunk000Sub001Block065Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part019] using hcert

def TailChunk000Sub001Block065Part020SupportExplicit : Finset ℕ :=
  ([10981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part020 : ℚ :=
  (2474612675 : ℚ) / 1243248234258386304

def SurrogateDiagonalTailChunk000Sub001Block065Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10981
    = surrogateDiagTailX0RatChunk000Sub001Block065Part020

theorem surrogateDiagonalTailChunk000Sub001Block065Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part020] using hcert

def TailChunk000Sub001Block065Part021SupportExplicit : Finset ℕ :=
  ([10983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part021 : ℚ :=
  (453181272875 : ℚ) / 1924880883432367104

def SurrogateDiagonalTailChunk000Sub001Block065Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10983
    = surrogateDiagTailX0RatChunk000Sub001Block065Part021

theorem surrogateDiagonalTailChunk000Sub001Block065Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part021] using hcert

def TailChunk000Sub001Block065Part022SupportExplicit : Finset ℕ :=
  ([10986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part022 : ℚ :=
  (2252909 : ℚ) / 2411690241600

def SurrogateDiagonalTailChunk000Sub001Block065Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10986
    = surrogateDiagTailX0RatChunk000Sub001Block065Part022

theorem surrogateDiagonalTailChunk000Sub001Block065Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part022] using hcert

def TailChunk000Sub001Block065Part023SupportExplicit : Finset ℕ :=
  ([10987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block065Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10987
    = surrogateDiagTailX0RatChunk000Sub001Block065Part023

theorem surrogateDiagonalTailChunk000Sub001Block065Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part023] using hcert

def TailChunk000Sub001Block065Part024SupportExplicit : Finset ℕ :=
  ([10990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block065Part024 : ℚ :=
  (35577306875 : ℚ) / 13647959289888768

def SurrogateDiagonalTailChunk000Sub001Block065Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10990
    = surrogateDiagTailX0RatChunk000Sub001Block065Part024

theorem surrogateDiagonalTailChunk000Sub001Block065Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block065Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block065Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block065Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block065Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block065Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block065HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block065Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block065Part000
    + surrogateDiagTailX0RatChunk000Sub001Block065Part001
    + surrogateDiagTailX0RatChunk000Sub001Block065Part002
    + surrogateDiagTailX0RatChunk000Sub001Block065Part003
    + surrogateDiagTailX0RatChunk000Sub001Block065Part004
    + surrogateDiagTailX0RatChunk000Sub001Block065Part005
    + surrogateDiagTailX0RatChunk000Sub001Block065Part006
    + surrogateDiagTailX0RatChunk000Sub001Block065Part007
    + surrogateDiagTailX0RatChunk000Sub001Block065Part008
    + surrogateDiagTailX0RatChunk000Sub001Block065Part009

def surrogateDiagonalTailChunk000Sub001Block065MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block065Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block065Part010
    + surrogateDiagTailX0RatChunk000Sub001Block065Part011
    + surrogateDiagTailX0RatChunk000Sub001Block065Part012
    + surrogateDiagTailX0RatChunk000Sub001Block065Part013
    + surrogateDiagTailX0RatChunk000Sub001Block065Part014
    + surrogateDiagTailX0RatChunk000Sub001Block065Part015
    + surrogateDiagTailX0RatChunk000Sub001Block065Part016
    + surrogateDiagTailX0RatChunk000Sub001Block065Part017
    + surrogateDiagTailX0RatChunk000Sub001Block065Part018
    + surrogateDiagTailX0RatChunk000Sub001Block065Part019

def surrogateDiagonalTailChunk000Sub001Block065TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block065Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block065Part020
    + surrogateDiagTailX0RatChunk000Sub001Block065Part021
    + surrogateDiagTailX0RatChunk000Sub001Block065Part022
    + surrogateDiagTailX0RatChunk000Sub001Block065Part023
    + surrogateDiagTailX0RatChunk000Sub001Block065Part024

def surrogateDiagonalTailChunk000Sub001Block065Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block065HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block065MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block065TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block065 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block065Part000
    + surrogateDiagTailX0RatChunk000Sub001Block065Part001
    + surrogateDiagTailX0RatChunk000Sub001Block065Part002
    + surrogateDiagTailX0RatChunk000Sub001Block065Part003
    + surrogateDiagTailX0RatChunk000Sub001Block065Part004
    + surrogateDiagTailX0RatChunk000Sub001Block065Part005
    + surrogateDiagTailX0RatChunk000Sub001Block065Part006
    + surrogateDiagTailX0RatChunk000Sub001Block065Part007
    + surrogateDiagTailX0RatChunk000Sub001Block065Part008
    + surrogateDiagTailX0RatChunk000Sub001Block065Part009
    + surrogateDiagTailX0RatChunk000Sub001Block065Part010
    + surrogateDiagTailX0RatChunk000Sub001Block065Part011
    + surrogateDiagTailX0RatChunk000Sub001Block065Part012
    + surrogateDiagTailX0RatChunk000Sub001Block065Part013
    + surrogateDiagTailX0RatChunk000Sub001Block065Part014
    + surrogateDiagTailX0RatChunk000Sub001Block065Part015
    + surrogateDiagTailX0RatChunk000Sub001Block065Part016
    + surrogateDiagTailX0RatChunk000Sub001Block065Part017
    + surrogateDiagTailX0RatChunk000Sub001Block065Part018
    + surrogateDiagTailX0RatChunk000Sub001Block065Part019
    + surrogateDiagTailX0RatChunk000Sub001Block065Part020
    + surrogateDiagTailX0RatChunk000Sub001Block065Part021
    + surrogateDiagTailX0RatChunk000Sub001Block065Part022
    + surrogateDiagTailX0RatChunk000Sub001Block065Part023
    + surrogateDiagTailX0RatChunk000Sub001Block065Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block065_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block065Head + surrogateDiagTailX0RatChunk000Sub001Block065Mid + surrogateDiagTailX0RatChunk000Sub001Block065Tail =
      surrogateDiagTailX0RatChunk000Sub001Block065 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block065Head surrogateDiagTailX0RatChunk000Sub001Block065Mid surrogateDiagTailX0RatChunk000Sub001Block065Tail surrogateDiagTailX0RatChunk000Sub001Block065
  ring

def SurrogateDiagonalTailChunk000Sub001Block065HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block065HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block065Head

def SurrogateDiagonalTailChunk000Sub001Block065MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block065MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block065Mid

def SurrogateDiagonalTailChunk000Sub001Block065TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block065TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block065Tail

theorem surrogateDiagonalTailChunk000Sub001Block065_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block065HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block065MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block065TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block065Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block065 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block065HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block065MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block065TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block065Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block065_eq_head_add_mid_add_tail

/-- Block 066 covers tail-support indices [6650,6675) and q from 10991 to 11029. -/

def TailChunk000Sub001Block066Part000SupportExplicit : Finset ℕ :=
  ([10991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part000 : ℚ :=
  (185335375 : ℚ) / 46693551825716544

def SurrogateDiagonalTailChunk000Sub001Block066Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10991
    = surrogateDiagTailX0RatChunk000Sub001Block066Part000

theorem surrogateDiagonalTailChunk000Sub001Block066Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part000] using hcert

def TailChunk000Sub001Block066Part001SupportExplicit : Finset ℕ :=
  ([10993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block066Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10993
    = surrogateDiagTailX0RatChunk000Sub001Block066Part001

theorem surrogateDiagonalTailChunk000Sub001Block066Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part001] using hcert

def TailChunk000Sub001Block066Part002SupportExplicit : Finset ℕ :=
  ([10994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part002 : ℚ :=
  (223491058925 : ℚ) / 234928347263077776

def SurrogateDiagonalTailChunk000Sub001Block066Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10994
    = surrogateDiagTailX0RatChunk000Sub001Block066Part002

theorem surrogateDiagonalTailChunk000Sub001Block066Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part002] using hcert

def TailChunk000Sub001Block066Part003SupportExplicit : Finset ℕ :=
  ([10995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part003 : ℚ :=
  (906715789975 : ℚ) / 2940567351785422848

def SurrogateDiagonalTailChunk000Sub001Block066Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10995
    = surrogateDiagTailX0RatChunk000Sub001Block066Part003

theorem surrogateDiagonalTailChunk000Sub001Block066Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part003] using hcert

def TailChunk000Sub001Block066Part004SupportExplicit : Finset ℕ :=
  ([10997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part004 : ℚ :=
  (1030796683 : ℚ) / 43754019526094400

def SurrogateDiagonalTailChunk000Sub001Block066Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10997
    = surrogateDiagTailX0RatChunk000Sub001Block066Part004

theorem surrogateDiagonalTailChunk000Sub001Block066Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part004] using hcert

def TailChunk000Sub001Block066Part005SupportExplicit : Finset ℕ :=
  ([10999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part005 : ℚ :=
  (11229679975 : ℚ) / 1502046094905311232

def SurrogateDiagonalTailChunk000Sub001Block066Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 10999
    = surrogateDiagTailX0RatChunk000Sub001Block066Part005

theorem surrogateDiagonalTailChunk000Sub001Block066Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part005] using hcert

def TailChunk000Sub001Block066Part006SupportExplicit : Finset ℕ :=
  ([11001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part006 : ℚ :=
  (32501180125 : ℚ) / 211386872138563584

def SurrogateDiagonalTailChunk000Sub001Block066Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11001
    = surrogateDiagTailX0RatChunk000Sub001Block066Part006

theorem surrogateDiagonalTailChunk000Sub001Block066Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part006] using hcert

def TailChunk000Sub001Block066Part007SupportExplicit : Finset ℕ :=
  ([11002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part007 : ℚ :=
  (30261001 : ℚ) / 36609820500000

def SurrogateDiagonalTailChunk000Sub001Block066Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11002
    = surrogateDiagTailX0RatChunk000Sub001Block066Part007

theorem surrogateDiagonalTailChunk000Sub001Block066Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part007] using hcert

def TailChunk000Sub001Block066Part008SupportExplicit : Finset ℕ :=
  ([11003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block066Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11003
    = surrogateDiagTailX0RatChunk000Sub001Block066Part008

theorem surrogateDiagonalTailChunk000Sub001Block066Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part008] using hcert

def TailChunk000Sub001Block066Part009SupportExplicit : Finset ℕ :=
  ([11005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part009 : ℚ :=
  (26969875699 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk000Sub001Block066Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11005
    = surrogateDiagTailX0RatChunk000Sub001Block066Part009

theorem surrogateDiagonalTailChunk000Sub001Block066Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part009] using hcert

def TailChunk000Sub001Block066Part010SupportExplicit : Finset ℕ :=
  ([11006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part010 : ℚ :=
  (473172015625 : ℚ) / 572860940638282002

def SurrogateDiagonalTailChunk000Sub001Block066Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11006
    = surrogateDiagTailX0RatChunk000Sub001Block066Part010

theorem surrogateDiagonalTailChunk000Sub001Block066Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part010] using hcert

def TailChunk000Sub001Block066Part011SupportExplicit : Finset ℕ :=
  ([11009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part011 : ℚ :=
  (16195789 : ℚ) / 8504756611200000

def SurrogateDiagonalTailChunk000Sub001Block066Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11009
    = surrogateDiagTailX0RatChunk000Sub001Block066Part011

theorem surrogateDiagonalTailChunk000Sub001Block066Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part011] using hcert

def TailChunk000Sub001Block066Part012SupportExplicit : Finset ℕ :=
  ([11010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part012 : ℚ :=
  (324620563525 : ℚ) / 61261819828862976

def SurrogateDiagonalTailChunk000Sub001Block066Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11010
    = surrogateDiagTailX0RatChunk000Sub001Block066Part012

theorem surrogateDiagonalTailChunk000Sub001Block066Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part012] using hcert

def TailChunk000Sub001Block066Part013SupportExplicit : Finset ℕ :=
  ([11013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part013 : ℚ :=
  (3369725383 : ℚ) / 29031607914150720

def SurrogateDiagonalTailChunk000Sub001Block066Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11013
    = surrogateDiagTailX0RatChunk000Sub001Block066Part013

theorem surrogateDiagonalTailChunk000Sub001Block066Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part013] using hcert

def TailChunk000Sub001Block066Part014SupportExplicit : Finset ℕ :=
  ([11014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part014 : ℚ :=
  (473860140625 : ℚ) / 574528656975654162

def SurrogateDiagonalTailChunk000Sub001Block066Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11014
    = surrogateDiagTailX0RatChunk000Sub001Block066Part014

theorem surrogateDiagonalTailChunk000Sub001Block066Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part014] using hcert

def TailChunk000Sub001Block066Part015SupportExplicit : Finset ℕ :=
  ([11015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part015 : ℚ :=
  (227509248925 : ℚ) / 3762496385673933312

def SurrogateDiagonalTailChunk000Sub001Block066Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11015
    = surrogateDiagTailX0RatChunk000Sub001Block066Part015

theorem surrogateDiagonalTailChunk000Sub001Block066Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part015] using hcert

def TailChunk000Sub001Block066Part016SupportExplicit : Finset ℕ :=
  ([11017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part016 : ℚ :=
  (27272064675 : ℚ) / 5096569116708648128

def SurrogateDiagonalTailChunk000Sub001Block066Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11017
    = surrogateDiagTailX0RatChunk000Sub001Block066Part016

theorem surrogateDiagonalTailChunk000Sub001Block066Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part016] using hcert

def TailChunk000Sub001Block066Part017SupportExplicit : Finset ℕ :=
  ([11018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part017 : ℚ :=
  (1585283318575 : ℚ) / 1236864271665495168

def SurrogateDiagonalTailChunk000Sub001Block066Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11018
    = surrogateDiagTailX0RatChunk000Sub001Block066Part017

theorem surrogateDiagonalTailChunk000Sub001Block066Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part017] using hcert

def TailChunk000Sub001Block066Part018SupportExplicit : Finset ℕ :=
  ([11019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part018 : ℚ :=
  (210837273925 : ℚ) / 1818433988925530112

def SurrogateDiagonalTailChunk000Sub001Block066Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11019
    = surrogateDiagTailX0RatChunk000Sub001Block066Part018

theorem surrogateDiagonalTailChunk000Sub001Block066Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part018] using hcert

def TailChunk000Sub001Block066Part019SupportExplicit : Finset ℕ :=
  ([11021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part019 : ℚ :=
  (64228270075 : ℚ) / 34170474297389655168

def SurrogateDiagonalTailChunk000Sub001Block066Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11021
    = surrogateDiagTailX0RatChunk000Sub001Block066Part019

theorem surrogateDiagonalTailChunk000Sub001Block066Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part019] using hcert

def TailChunk000Sub001Block066Part020SupportExplicit : Finset ℕ :=
  ([11022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part020 : ℚ :=
  (6368799783 : ℚ) / 2025293340339200

def SurrogateDiagonalTailChunk000Sub001Block066Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11022
    = surrogateDiagTailX0RatChunk000Sub001Block066Part020

theorem surrogateDiagonalTailChunk000Sub001Block066Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part020] using hcert

def TailChunk000Sub001Block066Part021SupportExplicit : Finset ℕ :=
  ([11023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part021 : ℚ :=
  (1369049249 : ℚ) / 680380528896000000

def SurrogateDiagonalTailChunk000Sub001Block066Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11023
    = surrogateDiagTailX0RatChunk000Sub001Block066Part021

theorem surrogateDiagonalTailChunk000Sub001Block066Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part021] using hcert

def TailChunk000Sub001Block066Part022SupportExplicit : Finset ℕ :=
  ([11026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part022 : ℚ :=
  (2119121075 : ℚ) / 2332222500989952

def SurrogateDiagonalTailChunk000Sub001Block066Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11026
    = surrogateDiagTailX0RatChunk000Sub001Block066Part022

theorem surrogateDiagonalTailChunk000Sub001Block066Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part022] using hcert

def TailChunk000Sub001Block066Part023SupportExplicit : Finset ℕ :=
  ([11027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block066Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11027
    = surrogateDiagTailX0RatChunk000Sub001Block066Part023

theorem surrogateDiagonalTailChunk000Sub001Block066Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part023] using hcert

def TailChunk000Sub001Block066Part024SupportExplicit : Finset ℕ :=
  ([11029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block066Part024 : ℚ :=
  (649917681 : ℚ) / 220147998438195200

def SurrogateDiagonalTailChunk000Sub001Block066Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11029
    = surrogateDiagTailX0RatChunk000Sub001Block066Part024

theorem surrogateDiagonalTailChunk000Sub001Block066Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block066Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block066Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block066Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block066Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block066Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block066HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block066Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block066Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block066Part000
    + surrogateDiagTailX0RatChunk000Sub001Block066Part001
    + surrogateDiagTailX0RatChunk000Sub001Block066Part002
    + surrogateDiagTailX0RatChunk000Sub001Block066Part003
    + surrogateDiagTailX0RatChunk000Sub001Block066Part004
    + surrogateDiagTailX0RatChunk000Sub001Block066Part005
    + surrogateDiagTailX0RatChunk000Sub001Block066Part006
    + surrogateDiagTailX0RatChunk000Sub001Block066Part007
    + surrogateDiagTailX0RatChunk000Sub001Block066Part008
    + surrogateDiagTailX0RatChunk000Sub001Block066Part009

def surrogateDiagonalTailChunk000Sub001Block066MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block066Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block066Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block066Part010
    + surrogateDiagTailX0RatChunk000Sub001Block066Part011
    + surrogateDiagTailX0RatChunk000Sub001Block066Part012
    + surrogateDiagTailX0RatChunk000Sub001Block066Part013
    + surrogateDiagTailX0RatChunk000Sub001Block066Part014
    + surrogateDiagTailX0RatChunk000Sub001Block066Part015
    + surrogateDiagTailX0RatChunk000Sub001Block066Part016
    + surrogateDiagTailX0RatChunk000Sub001Block066Part017
    + surrogateDiagTailX0RatChunk000Sub001Block066Part018
    + surrogateDiagTailX0RatChunk000Sub001Block066Part019

def surrogateDiagonalTailChunk000Sub001Block066TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block066Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block066Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block066Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block066Part020
    + surrogateDiagTailX0RatChunk000Sub001Block066Part021
    + surrogateDiagTailX0RatChunk000Sub001Block066Part022
    + surrogateDiagTailX0RatChunk000Sub001Block066Part023
    + surrogateDiagTailX0RatChunk000Sub001Block066Part024

def surrogateDiagonalTailChunk000Sub001Block066Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block066HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block066MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block066TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block066 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block066Part000
    + surrogateDiagTailX0RatChunk000Sub001Block066Part001
    + surrogateDiagTailX0RatChunk000Sub001Block066Part002
    + surrogateDiagTailX0RatChunk000Sub001Block066Part003
    + surrogateDiagTailX0RatChunk000Sub001Block066Part004
    + surrogateDiagTailX0RatChunk000Sub001Block066Part005
    + surrogateDiagTailX0RatChunk000Sub001Block066Part006
    + surrogateDiagTailX0RatChunk000Sub001Block066Part007
    + surrogateDiagTailX0RatChunk000Sub001Block066Part008
    + surrogateDiagTailX0RatChunk000Sub001Block066Part009
    + surrogateDiagTailX0RatChunk000Sub001Block066Part010
    + surrogateDiagTailX0RatChunk000Sub001Block066Part011
    + surrogateDiagTailX0RatChunk000Sub001Block066Part012
    + surrogateDiagTailX0RatChunk000Sub001Block066Part013
    + surrogateDiagTailX0RatChunk000Sub001Block066Part014
    + surrogateDiagTailX0RatChunk000Sub001Block066Part015
    + surrogateDiagTailX0RatChunk000Sub001Block066Part016
    + surrogateDiagTailX0RatChunk000Sub001Block066Part017
    + surrogateDiagTailX0RatChunk000Sub001Block066Part018
    + surrogateDiagTailX0RatChunk000Sub001Block066Part019
    + surrogateDiagTailX0RatChunk000Sub001Block066Part020
    + surrogateDiagTailX0RatChunk000Sub001Block066Part021
    + surrogateDiagTailX0RatChunk000Sub001Block066Part022
    + surrogateDiagTailX0RatChunk000Sub001Block066Part023
    + surrogateDiagTailX0RatChunk000Sub001Block066Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block066_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block066Head + surrogateDiagTailX0RatChunk000Sub001Block066Mid + surrogateDiagTailX0RatChunk000Sub001Block066Tail =
      surrogateDiagTailX0RatChunk000Sub001Block066 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block066Head surrogateDiagTailX0RatChunk000Sub001Block066Mid surrogateDiagTailX0RatChunk000Sub001Block066Tail surrogateDiagTailX0RatChunk000Sub001Block066
  ring

def SurrogateDiagonalTailChunk000Sub001Block066HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block066HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block066Head

def SurrogateDiagonalTailChunk000Sub001Block066MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block066MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block066Mid

def SurrogateDiagonalTailChunk000Sub001Block066TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block066TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block066Tail

theorem surrogateDiagonalTailChunk000Sub001Block066_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block066HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block066MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block066TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block066Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block066 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block066HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block066MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block066TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block066Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block066_eq_head_add_mid_add_tail

/-- Block 067 covers tail-support indices [6675,6700) and q from 11030 to 11069. -/

def TailChunk000Sub001Block067Part000SupportExplicit : Finset ℕ :=
  ([11030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part000 : ℚ :=
  (360907033975 : ℚ) / 236011524900966912

def SurrogateDiagonalTailChunk000Sub001Block067Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11030
    = surrogateDiagTailX0RatChunk000Sub001Block067Part000

theorem surrogateDiagonalTailChunk000Sub001Block067Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part000] using hcert

def TailChunk000Sub001Block067Part001SupportExplicit : Finset ℕ :=
  ([11031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part001 : ℚ :=
  (844704466475 : ℚ) / 3652740809613026304

def SurrogateDiagonalTailChunk000Sub001Block067Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11031
    = surrogateDiagTailX0RatChunk000Sub001Block067Part001

theorem surrogateDiagonalTailChunk000Sub001Block067Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part001] using hcert

def TailChunk000Sub001Block067Part002SupportExplicit : Finset ℕ :=
  ([11033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part002 : ℚ :=
  (20099815843 : ℚ) / 741786209432371200

def SurrogateDiagonalTailChunk000Sub001Block067Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11033
    = surrogateDiagTailX0RatChunk000Sub001Block067Part002

theorem surrogateDiagonalTailChunk000Sub001Block067Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part002] using hcert

def TailChunk000Sub001Block067Part003SupportExplicit : Finset ℕ :=
  ([11035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part003 : ℚ :=
  (609433302025 : ℚ) / 15159638900457228288

def SurrogateDiagonalTailChunk000Sub001Block067Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11035
    = surrogateDiagTailX0RatChunk000Sub001Block067Part003

theorem surrogateDiagonalTailChunk000Sub001Block067Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part003] using hcert

def TailChunk000Sub001Block067Part004SupportExplicit : Finset ℕ :=
  ([11037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part004 : ℚ :=
  (1607545654375 : ℚ) / 5246482867553599488

def SurrogateDiagonalTailChunk000Sub001Block067Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11037
    = surrogateDiagTailX0RatChunk000Sub001Block067Part004

theorem surrogateDiagonalTailChunk000Sub001Block067Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part004] using hcert

def TailChunk000Sub001Block067Part005SupportExplicit : Finset ℕ :=
  ([11038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part005 : ℚ :=
  (475927515625 : ℚ) / 579553659059911122

def SurrogateDiagonalTailChunk000Sub001Block067Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11038
    = surrogateDiagTailX0RatChunk000Sub001Block067Part005

theorem surrogateDiagonalTailChunk000Sub001Block067Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part005] using hcert

def TailChunk000Sub001Block067Part006SupportExplicit : Finset ℕ :=
  ([11039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part006 : ℚ :=
  (149469297775 : ℚ) / 3845185527427379712

def SurrogateDiagonalTailChunk000Sub001Block067Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11039
    = surrogateDiagTailX0RatChunk000Sub001Block067Part006

theorem surrogateDiagonalTailChunk000Sub001Block067Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part006] using hcert

def TailChunk000Sub001Block067Part007SupportExplicit : Finset ℕ :=
  ([11041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part007 : ℚ :=
  (601196753 : ℚ) / 272152211558400000

def SurrogateDiagonalTailChunk000Sub001Block067Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11041
    = surrogateDiagTailX0RatChunk000Sub001Block067Part007

theorem surrogateDiagonalTailChunk000Sub001Block067Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part007] using hcert

def TailChunk000Sub001Block067Part008SupportExplicit : Finset ℕ :=
  ([11042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part008 : ℚ :=
  (762036025 : ℚ) / 928630965215232

def SurrogateDiagonalTailChunk000Sub001Block067Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11042
    = surrogateDiagTailX0RatChunk000Sub001Block067Part008

theorem surrogateDiagonalTailChunk000Sub001Block067Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part008] using hcert

def TailChunk000Sub001Block067Part009SupportExplicit : Finset ℕ :=
  ([11046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part009 : ℚ :=
  (269126887675 : ℚ) / 61079717119283712

def SurrogateDiagonalTailChunk000Sub001Block067Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11046
    = surrogateDiagTailX0RatChunk000Sub001Block067Part009

theorem surrogateDiagonalTailChunk000Sub001Block067Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part009] using hcert

def TailChunk000Sub001Block067Part010SupportExplicit : Finset ℕ :=
  ([11047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block067Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11047
    = surrogateDiagTailX0RatChunk000Sub001Block067Part010

theorem surrogateDiagonalTailChunk000Sub001Block067Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part010] using hcert

def TailChunk000Sub001Block067Part011SupportExplicit : Finset ℕ :=
  ([11049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part011 : ℚ :=
  (1648223756275 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk000Sub001Block067Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11049
    = surrogateDiagTailX0RatChunk000Sub001Block067Part011

theorem surrogateDiagonalTailChunk000Sub001Block067Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part011] using hcert

def TailChunk000Sub001Block067Part012SupportExplicit : Finset ℕ :=
  ([11051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part012 : ℚ :=
  (45371899175 : ℚ) / 16709131852006293504

def SurrogateDiagonalTailChunk000Sub001Block067Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11051
    = surrogateDiagTailX0RatChunk000Sub001Block067Part012

theorem surrogateDiagonalTailChunk000Sub001Block067Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part012] using hcert

def TailChunk000Sub001Block067Part013SupportExplicit : Finset ℕ :=
  ([11053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part013 : ℚ :=
  (8677381825 : ℚ) / 372105505843284672

def SurrogateDiagonalTailChunk000Sub001Block067Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11053
    = surrogateDiagTailX0RatChunk000Sub001Block067Part013

theorem surrogateDiagonalTailChunk000Sub001Block067Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part013] using hcert

def TailChunk000Sub001Block067Part014SupportExplicit : Finset ℕ :=
  ([11054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part014 : ℚ :=
  (477308265625 : ℚ) / 582921924278251122

def SurrogateDiagonalTailChunk000Sub001Block067Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11054
    = surrogateDiagTailX0RatChunk000Sub001Block067Part014

theorem surrogateDiagonalTailChunk000Sub001Block067Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part014] using hcert

def TailChunk000Sub001Block067Part015SupportExplicit : Finset ℕ :=
  ([11055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part015 : ℚ :=
  (53867174641 : ℚ) / 77736062759731200

def SurrogateDiagonalTailChunk000Sub001Block067Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11055
    = surrogateDiagTailX0RatChunk000Sub001Block067Part015

theorem surrogateDiagonalTailChunk000Sub001Block067Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part015] using hcert

def TailChunk000Sub001Block067Part016SupportExplicit : Finset ℕ :=
  ([11057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block067Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11057
    = surrogateDiagTailX0RatChunk000Sub001Block067Part016

theorem surrogateDiagonalTailChunk000Sub001Block067Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part016] using hcert

def TailChunk000Sub001Block067Part017SupportExplicit : Finset ℕ :=
  ([11058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part017 : ℚ :=
  (131887738825 : ℚ) / 39635038525980672

def SurrogateDiagonalTailChunk000Sub001Block067Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11058
    = surrogateDiagTailX0RatChunk000Sub001Block067Part017

theorem surrogateDiagonalTailChunk000Sub001Block067Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part017] using hcert

def TailChunk000Sub001Block067Part018SupportExplicit : Finset ℕ :=
  ([11059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block067Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11059
    = surrogateDiagTailX0RatChunk000Sub001Block067Part018

theorem surrogateDiagonalTailChunk000Sub001Block067Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part018] using hcert

def TailChunk000Sub001Block067Part019SupportExplicit : Finset ℕ :=
  ([11062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part019 : ℚ :=
  (764799025 : ℚ) / 935378483098962

def SurrogateDiagonalTailChunk000Sub001Block067Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11062
    = surrogateDiagTailX0RatChunk000Sub001Block067Part019

theorem surrogateDiagonalTailChunk000Sub001Block067Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part019] using hcert

def TailChunk000Sub001Block067Part020SupportExplicit : Finset ℕ :=
  ([11063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part020 : ℚ :=
  (6116778725 : ℚ) / 283347948759220224

def SurrogateDiagonalTailChunk000Sub001Block067Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11063
    = surrogateDiagTailX0RatChunk000Sub001Block067Part020

theorem surrogateDiagonalTailChunk000Sub001Block067Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part020] using hcert

def TailChunk000Sub001Block067Part021SupportExplicit : Finset ℕ :=
  ([11065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part021 : ℚ :=
  (65593566425 : ℚ) / 1094660076220956672

def SurrogateDiagonalTailChunk000Sub001Block067Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11065
    = surrogateDiagTailX0RatChunk000Sub001Block067Part021

theorem surrogateDiagonalTailChunk000Sub001Block067Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part021] using hcert

def TailChunk000Sub001Block067Part022SupportExplicit : Finset ℕ :=
  ([11066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part022 : ℚ :=
  (22726352061 : ℚ) / 21172905739734400

def SurrogateDiagonalTailChunk000Sub001Block067Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11066
    = surrogateDiagTailX0RatChunk000Sub001Block067Part022

theorem surrogateDiagonalTailChunk000Sub001Block067Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part022] using hcert

def TailChunk000Sub001Block067Part023SupportExplicit : Finset ℕ :=
  ([11067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part023 : ℚ :=
  (11585831 : ℚ) / 33980657172480

def SurrogateDiagonalTailChunk000Sub001Block067Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11067
    = surrogateDiagTailX0RatChunk000Sub001Block067Part023

theorem surrogateDiagonalTailChunk000Sub001Block067Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part023] using hcert

def TailChunk000Sub001Block067Part024SupportExplicit : Finset ℕ :=
  ([11069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block067Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block067Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11069
    = surrogateDiagTailX0RatChunk000Sub001Block067Part024

theorem surrogateDiagonalTailChunk000Sub001Block067Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block067Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block067Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block067Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block067Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block067Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block067HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block067Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block067Part000
    + surrogateDiagTailX0RatChunk000Sub001Block067Part001
    + surrogateDiagTailX0RatChunk000Sub001Block067Part002
    + surrogateDiagTailX0RatChunk000Sub001Block067Part003
    + surrogateDiagTailX0RatChunk000Sub001Block067Part004
    + surrogateDiagTailX0RatChunk000Sub001Block067Part005
    + surrogateDiagTailX0RatChunk000Sub001Block067Part006
    + surrogateDiagTailX0RatChunk000Sub001Block067Part007
    + surrogateDiagTailX0RatChunk000Sub001Block067Part008
    + surrogateDiagTailX0RatChunk000Sub001Block067Part009

def surrogateDiagonalTailChunk000Sub001Block067MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block067Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block067Part010
    + surrogateDiagTailX0RatChunk000Sub001Block067Part011
    + surrogateDiagTailX0RatChunk000Sub001Block067Part012
    + surrogateDiagTailX0RatChunk000Sub001Block067Part013
    + surrogateDiagTailX0RatChunk000Sub001Block067Part014
    + surrogateDiagTailX0RatChunk000Sub001Block067Part015
    + surrogateDiagTailX0RatChunk000Sub001Block067Part016
    + surrogateDiagTailX0RatChunk000Sub001Block067Part017
    + surrogateDiagTailX0RatChunk000Sub001Block067Part018
    + surrogateDiagTailX0RatChunk000Sub001Block067Part019

def surrogateDiagonalTailChunk000Sub001Block067TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block067Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block067Part020
    + surrogateDiagTailX0RatChunk000Sub001Block067Part021
    + surrogateDiagTailX0RatChunk000Sub001Block067Part022
    + surrogateDiagTailX0RatChunk000Sub001Block067Part023
    + surrogateDiagTailX0RatChunk000Sub001Block067Part024

def surrogateDiagonalTailChunk000Sub001Block067Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block067HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block067MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block067TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block067 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block067Part000
    + surrogateDiagTailX0RatChunk000Sub001Block067Part001
    + surrogateDiagTailX0RatChunk000Sub001Block067Part002
    + surrogateDiagTailX0RatChunk000Sub001Block067Part003
    + surrogateDiagTailX0RatChunk000Sub001Block067Part004
    + surrogateDiagTailX0RatChunk000Sub001Block067Part005
    + surrogateDiagTailX0RatChunk000Sub001Block067Part006
    + surrogateDiagTailX0RatChunk000Sub001Block067Part007
    + surrogateDiagTailX0RatChunk000Sub001Block067Part008
    + surrogateDiagTailX0RatChunk000Sub001Block067Part009
    + surrogateDiagTailX0RatChunk000Sub001Block067Part010
    + surrogateDiagTailX0RatChunk000Sub001Block067Part011
    + surrogateDiagTailX0RatChunk000Sub001Block067Part012
    + surrogateDiagTailX0RatChunk000Sub001Block067Part013
    + surrogateDiagTailX0RatChunk000Sub001Block067Part014
    + surrogateDiagTailX0RatChunk000Sub001Block067Part015
    + surrogateDiagTailX0RatChunk000Sub001Block067Part016
    + surrogateDiagTailX0RatChunk000Sub001Block067Part017
    + surrogateDiagTailX0RatChunk000Sub001Block067Part018
    + surrogateDiagTailX0RatChunk000Sub001Block067Part019
    + surrogateDiagTailX0RatChunk000Sub001Block067Part020
    + surrogateDiagTailX0RatChunk000Sub001Block067Part021
    + surrogateDiagTailX0RatChunk000Sub001Block067Part022
    + surrogateDiagTailX0RatChunk000Sub001Block067Part023
    + surrogateDiagTailX0RatChunk000Sub001Block067Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block067_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block067Head + surrogateDiagTailX0RatChunk000Sub001Block067Mid + surrogateDiagTailX0RatChunk000Sub001Block067Tail =
      surrogateDiagTailX0RatChunk000Sub001Block067 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block067Head surrogateDiagTailX0RatChunk000Sub001Block067Mid surrogateDiagTailX0RatChunk000Sub001Block067Tail surrogateDiagTailX0RatChunk000Sub001Block067
  ring

def SurrogateDiagonalTailChunk000Sub001Block067HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block067HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block067Head

def SurrogateDiagonalTailChunk000Sub001Block067MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block067MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block067Mid

def SurrogateDiagonalTailChunk000Sub001Block067TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block067TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block067Tail

theorem surrogateDiagonalTailChunk000Sub001Block067_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block067HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block067MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block067TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block067Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block067 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block067HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block067MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block067TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block067Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block067_eq_head_add_mid_add_tail

/-- Block 068 covers tail-support indices [6700,6725) and q from 11071 to 11113. -/

def TailChunk000Sub001Block068Part000SupportExplicit : Finset ℕ :=
  ([11071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block068Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11071
    = surrogateDiagTailX0RatChunk000Sub001Block068Part000

theorem surrogateDiagonalTailChunk000Sub001Block068Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part000] using hcert

def TailChunk000Sub001Block068Part001SupportExplicit : Finset ℕ :=
  ([11073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part001 : ℚ :=
  (3406525381 : ℚ) / 29669641415334720

def SurrogateDiagonalTailChunk000Sub001Block068Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11073
    = surrogateDiagTailX0RatChunk000Sub001Block068Part001

theorem surrogateDiagonalTailChunk000Sub001Block068Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part001] using hcert

def TailChunk000Sub001Block068Part002SupportExplicit : Finset ℕ :=
  ([11077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part002 : ℚ :=
  (6607495717 : ℚ) / 255899236685414400

def SurrogateDiagonalTailChunk000Sub001Block068Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11077
    = surrogateDiagTailX0RatChunk000Sub001Block068Part002

theorem surrogateDiagonalTailChunk000Sub001Block068Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part002] using hcert

def TailChunk000Sub001Block068Part003SupportExplicit : Finset ℕ :=
  ([11078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part003 : ℚ :=
  (5240994299 : ℚ) / 5722757506636800

def SurrogateDiagonalTailChunk000Sub001Block068Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11078
    = surrogateDiagTailX0RatChunk000Sub001Block068Part003

theorem surrogateDiagonalTailChunk000Sub001Block068Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part003] using hcert

def TailChunk000Sub001Block068Part004SupportExplicit : Finset ℕ :=
  ([11081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part004 : ℚ :=
  (627179995525 : ℚ) / 20298211671938514048

def SurrogateDiagonalTailChunk000Sub001Block068Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11081
    = surrogateDiagTailX0RatChunk000Sub001Block068Part004

theorem surrogateDiagonalTailChunk000Sub001Block068Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part004] using hcert

def TailChunk000Sub001Block068Part005SupportExplicit : Finset ℕ :=
  ([11082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part005 : ℚ :=
  (127851825 : ℚ) / 46450113346624

def SurrogateDiagonalTailChunk000Sub001Block068Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11082
    = surrogateDiagTailX0RatChunk000Sub001Block068Part005

theorem surrogateDiagonalTailChunk000Sub001Block068Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part005] using hcert

def TailChunk000Sub001Block068Part006SupportExplicit : Finset ℕ :=
  ([11083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block068Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11083
    = surrogateDiagTailX0RatChunk000Sub001Block068Part006

theorem surrogateDiagonalTailChunk000Sub001Block068Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part006] using hcert

def TailChunk000Sub001Block068Part007SupportExplicit : Finset ℕ :=
  ([11085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part007 : ℚ :=
  (318569337875 : ℚ) / 1012723760310091776

def SurrogateDiagonalTailChunk000Sub001Block068Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11085
    = surrogateDiagTailX0RatChunk000Sub001Block068Part007

theorem surrogateDiagonalTailChunk000Sub001Block068Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part007] using hcert

def TailChunk000Sub001Block068Part008SupportExplicit : Finset ℕ :=
  ([11086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part008 : ℚ :=
  (4047984379 : ℚ) / 4318670153318400

def SurrogateDiagonalTailChunk000Sub001Block068Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11086
    = surrogateDiagTailX0RatChunk000Sub001Block068Part008

theorem surrogateDiagonalTailChunk000Sub001Block068Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part008] using hcert

def TailChunk000Sub001Block068Part009SupportExplicit : Finset ℕ :=
  ([11087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block068Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11087
    = surrogateDiagTailX0RatChunk000Sub001Block068Part009

theorem surrogateDiagonalTailChunk000Sub001Block068Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part009] using hcert

def TailChunk000Sub001Block068Part010SupportExplicit : Finset ℕ :=
  ([11089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part010 : ℚ :=
  (275694382375 : ℚ) / 27321857515324735488

def SurrogateDiagonalTailChunk000Sub001Block068Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11089
    = surrogateDiagTailX0RatChunk000Sub001Block068Part010

theorem surrogateDiagonalTailChunk000Sub001Block068Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part010] using hcert

def TailChunk000Sub001Block068Part011SupportExplicit : Finset ℕ :=
  ([11090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part011 : ℚ :=
  (768068457875 : ℚ) / 482387305176121344

def SurrogateDiagonalTailChunk000Sub001Block068Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11090
    = surrogateDiagTailX0RatChunk000Sub001Block068Part011

theorem surrogateDiagonalTailChunk000Sub001Block068Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part011] using hcert

def TailChunk000Sub001Block068Part012SupportExplicit : Finset ℕ :=
  ([11091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part012 : ℚ :=
  (30514324825 : ℚ) / 266634695265878016

def SurrogateDiagonalTailChunk000Sub001Block068Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11091
    = surrogateDiagTailX0RatChunk000Sub001Block068Part012

theorem surrogateDiagonalTailChunk000Sub001Block068Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part012] using hcert

def TailChunk000Sub001Block068Part013SupportExplicit : Finset ℕ :=
  ([11093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block068Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11093
    = surrogateDiagTailX0RatChunk000Sub001Block068Part013

theorem surrogateDiagonalTailChunk000Sub001Block068Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part013] using hcert

def TailChunk000Sub001Block068Part014SupportExplicit : Finset ℕ :=
  ([11095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part014 : ℚ :=
  (825020296375 : ℚ) / 8272183433133293568

def SurrogateDiagonalTailChunk000Sub001Block068Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11095
    = surrogateDiagTailX0RatChunk000Sub001Block068Part014

theorem surrogateDiagonalTailChunk000Sub001Block068Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part014] using hcert

def TailChunk000Sub001Block068Part015SupportExplicit : Finset ℕ :=
  ([11098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part015 : ℚ :=
  (18453578209 : ℚ) / 20332551781216800

def SurrogateDiagonalTailChunk000Sub001Block068Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11098
    = surrogateDiagTailX0RatChunk000Sub001Block068Part015

theorem surrogateDiagonalTailChunk000Sub001Block068Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part015] using hcert

def TailChunk000Sub001Block068Part016SupportExplicit : Finset ℕ :=
  ([11099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part016 : ℚ :=
  (106797679 : ℚ) / 8604937744220160

def SurrogateDiagonalTailChunk000Sub001Block068Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11099
    = surrogateDiagTailX0RatChunk000Sub001Block068Part016

theorem surrogateDiagonalTailChunk000Sub001Block068Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part016] using hcert

def TailChunk000Sub001Block068Part017SupportExplicit : Finset ℕ :=
  ([11101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part017 : ℚ :=
  (217252461925 : ℚ) / 29614006845139058688

def SurrogateDiagonalTailChunk000Sub001Block068Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11101
    = surrogateDiagTailX0RatChunk000Sub001Block068Part017

theorem surrogateDiagonalTailChunk000Sub001Block068Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part017] using hcert

def TailChunk000Sub001Block068Part018SupportExplicit : Finset ℕ :=
  ([11102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part018 : ℚ :=
  (1641013517 : ℚ) / 4354435384934400

def SurrogateDiagonalTailChunk000Sub001Block068Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11102
    = surrogateDiagTailX0RatChunk000Sub001Block068Part018

theorem surrogateDiagonalTailChunk000Sub001Block068Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part018] using hcert

def TailChunk000Sub001Block068Part019SupportExplicit : Finset ℕ :=
  ([11103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part019 : ℚ :=
  (171250019 : ℚ) / 1499628665760000

def SurrogateDiagonalTailChunk000Sub001Block068Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11103
    = surrogateDiagTailX0RatChunk000Sub001Block068Part019

theorem surrogateDiagonalTailChunk000Sub001Block068Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part019] using hcert

def TailChunk000Sub001Block068Part020SupportExplicit : Finset ℕ :=
  ([11105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part020 : ℚ :=
  (8229029983 : ℚ) / 207308666754662400

def SurrogateDiagonalTailChunk000Sub001Block068Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11105
    = surrogateDiagTailX0RatChunk000Sub001Block068Part020

theorem surrogateDiagonalTailChunk000Sub001Block068Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part020] using hcert

def TailChunk000Sub001Block068Part021SupportExplicit : Finset ℕ :=
  ([11107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part021 : ℚ :=
  (3969045125 : ℚ) / 1022733443311024704

def SurrogateDiagonalTailChunk000Sub001Block068Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11107
    = surrogateDiagTailX0RatChunk000Sub001Block068Part021

theorem surrogateDiagonalTailChunk000Sub001Block068Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part021] using hcert

def TailChunk000Sub001Block068Part022SupportExplicit : Finset ℕ :=
  ([11110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part022 : ℚ :=
  (5130741 : ℚ) / 8535040000000

def SurrogateDiagonalTailChunk000Sub001Block068Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11110
    = surrogateDiagTailX0RatChunk000Sub001Block068Part022

theorem surrogateDiagonalTailChunk000Sub001Block068Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part022] using hcert

def TailChunk000Sub001Block068Part023SupportExplicit : Finset ℕ :=
  ([11111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part023 : ℚ :=
  (376950631 : ℚ) / 136076105779200000

def SurrogateDiagonalTailChunk000Sub001Block068Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11111
    = surrogateDiagTailX0RatChunk000Sub001Block068Part023

theorem surrogateDiagonalTailChunk000Sub001Block068Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part023] using hcert

def TailChunk000Sub001Block068Part024SupportExplicit : Finset ℕ :=
  ([11113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block068Part024 : ℚ :=
  (1929668265625 : ℚ) / 9530941380979732992

def SurrogateDiagonalTailChunk000Sub001Block068Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11113
    = surrogateDiagTailX0RatChunk000Sub001Block068Part024

theorem surrogateDiagonalTailChunk000Sub001Block068Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block068Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block068Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block068Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block068Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block068Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block068HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block068Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block068Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block068Part000
    + surrogateDiagTailX0RatChunk000Sub001Block068Part001
    + surrogateDiagTailX0RatChunk000Sub001Block068Part002
    + surrogateDiagTailX0RatChunk000Sub001Block068Part003
    + surrogateDiagTailX0RatChunk000Sub001Block068Part004
    + surrogateDiagTailX0RatChunk000Sub001Block068Part005
    + surrogateDiagTailX0RatChunk000Sub001Block068Part006
    + surrogateDiagTailX0RatChunk000Sub001Block068Part007
    + surrogateDiagTailX0RatChunk000Sub001Block068Part008
    + surrogateDiagTailX0RatChunk000Sub001Block068Part009

def surrogateDiagonalTailChunk000Sub001Block068MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block068Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block068Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block068Part010
    + surrogateDiagTailX0RatChunk000Sub001Block068Part011
    + surrogateDiagTailX0RatChunk000Sub001Block068Part012
    + surrogateDiagTailX0RatChunk000Sub001Block068Part013
    + surrogateDiagTailX0RatChunk000Sub001Block068Part014
    + surrogateDiagTailX0RatChunk000Sub001Block068Part015
    + surrogateDiagTailX0RatChunk000Sub001Block068Part016
    + surrogateDiagTailX0RatChunk000Sub001Block068Part017
    + surrogateDiagTailX0RatChunk000Sub001Block068Part018
    + surrogateDiagTailX0RatChunk000Sub001Block068Part019

def surrogateDiagonalTailChunk000Sub001Block068TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block068Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block068Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block068Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block068Part020
    + surrogateDiagTailX0RatChunk000Sub001Block068Part021
    + surrogateDiagTailX0RatChunk000Sub001Block068Part022
    + surrogateDiagTailX0RatChunk000Sub001Block068Part023
    + surrogateDiagTailX0RatChunk000Sub001Block068Part024

def surrogateDiagonalTailChunk000Sub001Block068Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block068HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block068MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block068TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block068 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block068Part000
    + surrogateDiagTailX0RatChunk000Sub001Block068Part001
    + surrogateDiagTailX0RatChunk000Sub001Block068Part002
    + surrogateDiagTailX0RatChunk000Sub001Block068Part003
    + surrogateDiagTailX0RatChunk000Sub001Block068Part004
    + surrogateDiagTailX0RatChunk000Sub001Block068Part005
    + surrogateDiagTailX0RatChunk000Sub001Block068Part006
    + surrogateDiagTailX0RatChunk000Sub001Block068Part007
    + surrogateDiagTailX0RatChunk000Sub001Block068Part008
    + surrogateDiagTailX0RatChunk000Sub001Block068Part009
    + surrogateDiagTailX0RatChunk000Sub001Block068Part010
    + surrogateDiagTailX0RatChunk000Sub001Block068Part011
    + surrogateDiagTailX0RatChunk000Sub001Block068Part012
    + surrogateDiagTailX0RatChunk000Sub001Block068Part013
    + surrogateDiagTailX0RatChunk000Sub001Block068Part014
    + surrogateDiagTailX0RatChunk000Sub001Block068Part015
    + surrogateDiagTailX0RatChunk000Sub001Block068Part016
    + surrogateDiagTailX0RatChunk000Sub001Block068Part017
    + surrogateDiagTailX0RatChunk000Sub001Block068Part018
    + surrogateDiagTailX0RatChunk000Sub001Block068Part019
    + surrogateDiagTailX0RatChunk000Sub001Block068Part020
    + surrogateDiagTailX0RatChunk000Sub001Block068Part021
    + surrogateDiagTailX0RatChunk000Sub001Block068Part022
    + surrogateDiagTailX0RatChunk000Sub001Block068Part023
    + surrogateDiagTailX0RatChunk000Sub001Block068Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block068_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block068Head + surrogateDiagTailX0RatChunk000Sub001Block068Mid + surrogateDiagTailX0RatChunk000Sub001Block068Tail =
      surrogateDiagTailX0RatChunk000Sub001Block068 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block068Head surrogateDiagTailX0RatChunk000Sub001Block068Mid surrogateDiagTailX0RatChunk000Sub001Block068Tail surrogateDiagTailX0RatChunk000Sub001Block068
  ring

def SurrogateDiagonalTailChunk000Sub001Block068HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block068HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block068Head

def SurrogateDiagonalTailChunk000Sub001Block068MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block068MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block068Mid

def SurrogateDiagonalTailChunk000Sub001Block068TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block068TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block068Tail

theorem surrogateDiagonalTailChunk000Sub001Block068_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block068HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block068MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block068TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block068Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block068 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block068HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block068MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block068TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block068Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block068_eq_head_add_mid_add_tail

/-- Block 069 covers tail-support indices [6725,6750) and q from 11114 to 11157. -/

def TailChunk000Sub001Block069Part000SupportExplicit : Finset ℕ :=
  ([11114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part000 : ℚ :=
  (482503890625 : ℚ) / 595683836311233312

def SurrogateDiagonalTailChunk000Sub001Block069Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11114
    = surrogateDiagTailX0RatChunk000Sub001Block069Part000

theorem surrogateDiagonalTailChunk000Sub001Block069Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part000] using hcert

def TailChunk000Sub001Block069Part001SupportExplicit : Finset ℕ :=
  ([11117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part001 : ℚ :=
  (1931057640625 : ℚ) / 9544672250544520992

def SurrogateDiagonalTailChunk000Sub001Block069Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11117
    = surrogateDiagTailX0RatChunk000Sub001Block069Part001

theorem surrogateDiagonalTailChunk000Sub001Block069Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part001] using hcert

def TailChunk000Sub001Block069Part002SupportExplicit : Finset ℕ :=
  ([11118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part002 : ℚ :=
  (74490139675 : ℚ) / 22294709170864128

def SurrogateDiagonalTailChunk000Sub001Block069Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11118
    = surrogateDiagTailX0RatChunk000Sub001Block069Part002

theorem surrogateDiagonalTailChunk000Sub001Block069Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part002] using hcert

def TailChunk000Sub001Block069Part003SupportExplicit : Finset ℕ :=
  ([11119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part003 : ℚ :=
  (1931752515625 : ℚ) / 9551543246217520722

def SurrogateDiagonalTailChunk000Sub001Block069Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11119
    = surrogateDiagTailX0RatChunk000Sub001Block069Part003

theorem surrogateDiagonalTailChunk000Sub001Block069Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part003] using hcert

def TailChunk000Sub001Block069Part004SupportExplicit : Finset ℕ :=
  ([11121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part004 : ℚ :=
  (13464673 : ℚ) / 18500580016128

def SurrogateDiagonalTailChunk000Sub001Block069Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11121
    = surrogateDiagTailX0RatChunk000Sub001Block069Part004

theorem surrogateDiagonalTailChunk000Sub001Block069Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part004] using hcert

def TailChunk000Sub001Block069Part005SupportExplicit : Finset ℕ :=
  ([11122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part005 : ℚ :=
  (1876225730275 : ℚ) / 2145151703515632768

def SurrogateDiagonalTailChunk000Sub001Block069Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11122
    = surrogateDiagTailX0RatChunk000Sub001Block069Part005

theorem surrogateDiagonalTailChunk000Sub001Block069Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part005] using hcert

def TailChunk000Sub001Block069Part006SupportExplicit : Finset ℕ :=
  ([11126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part006 : ℚ :=
  (483546390625 : ℚ) / 598261155800709042

def SurrogateDiagonalTailChunk000Sub001Block069Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11126
    = surrogateDiagTailX0RatChunk000Sub001Block069Part006

theorem surrogateDiagonalTailChunk000Sub001Block069Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part006] using hcert

def TailChunk000Sub001Block069Part007SupportExplicit : Finset ℕ :=
  ([11127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part007 : ℚ :=
  (2148978653975 : ℚ) / 3781601379876086784

def SurrogateDiagonalTailChunk000Sub001Block069Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11127
    = surrogateDiagTailX0RatChunk000Sub001Block069Part007

theorem surrogateDiagonalTailChunk000Sub001Block069Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part007] using hcert

def TailChunk000Sub001Block069Part008SupportExplicit : Finset ℕ :=
  ([11129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part008 : ℚ :=
  (58589258879 : ℚ) / 266154596790503040

def SurrogateDiagonalTailChunk000Sub001Block069Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11129
    = surrogateDiagTailX0RatChunk000Sub001Block069Part008

theorem surrogateDiagonalTailChunk000Sub001Block069Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part008] using hcert

def TailChunk000Sub001Block069Part009SupportExplicit : Finset ℕ :=
  ([11130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part009 : ℚ :=
  (834723181375 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub001Block069Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11130
    = surrogateDiagTailX0RatChunk000Sub001Block069Part009

theorem surrogateDiagonalTailChunk000Sub001Block069Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part009] using hcert

def TailChunk000Sub001Block069Part010SupportExplicit : Finset ℕ :=
  ([11131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part010 : ℚ :=
  (3097479025 : ℚ) / 15348555450880722

def SurrogateDiagonalTailChunk000Sub001Block069Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11131
    = surrogateDiagTailX0RatChunk000Sub001Block069Part010

theorem surrogateDiagonalTailChunk000Sub001Block069Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part010] using hcert

def TailChunk000Sub001Block069Part011SupportExplicit : Finset ℕ :=
  ([11134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part011 : ℚ :=
  (1817819765875 : ℚ) / 1908307183337883648

def SurrogateDiagonalTailChunk000Sub001Block069Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11134
    = surrogateDiagTailX0RatChunk000Sub001Block069Part011

theorem surrogateDiagonalTailChunk000Sub001Block069Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part011] using hcert

def TailChunk000Sub001Block069Part012SupportExplicit : Finset ℕ :=
  ([11135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part012 : ℚ :=
  (189999025831 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk000Sub001Block069Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11135
    = surrogateDiagTailX0RatChunk000Sub001Block069Part012

theorem surrogateDiagonalTailChunk000Sub001Block069Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part012] using hcert

def TailChunk000Sub001Block069Part013SupportExplicit : Finset ℕ :=
  ([11137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part013 : ℚ :=
  (173878380575 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub001Block069Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11137
    = surrogateDiagTailX0RatChunk000Sub001Block069Part013

theorem surrogateDiagonalTailChunk000Sub001Block069Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part013] using hcert

def TailChunk000Sub001Block069Part014SupportExplicit : Finset ℕ :=
  ([11138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part014 : ℚ :=
  (484590015625 : ℚ) / 600846829640220672

def SurrogateDiagonalTailChunk000Sub001Block069Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11138
    = surrogateDiagTailX0RatChunk000Sub001Block069Part014

theorem surrogateDiagonalTailChunk000Sub001Block069Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part014] using hcert

def TailChunk000Sub001Block069Part015SupportExplicit : Finset ℕ :=
  ([11139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part015 : ℚ :=
  (4097545785625 : ℚ) / 6630657249378060288

def SurrogateDiagonalTailChunk000Sub001Block069Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11139
    = surrogateDiagTailX0RatChunk000Sub001Block069Part015

theorem surrogateDiagonalTailChunk000Sub001Block069Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part015] using hcert

def TailChunk000Sub001Block069Part016SupportExplicit : Finset ℕ :=
  ([11141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part016 : ℚ :=
  (6828264406825 : ℚ) / 27838568649290416128

def SurrogateDiagonalTailChunk000Sub001Block069Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11141
    = surrogateDiagTailX0RatChunk000Sub001Block069Part016

theorem surrogateDiagonalTailChunk000Sub001Block069Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part016] using hcert

def TailChunk000Sub001Block069Part017SupportExplicit : Finset ℕ :=
  ([11143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part017 : ℚ :=
  (266437128721 : ℚ) / 1049080706922547200

def SurrogateDiagonalTailChunk000Sub001Block069Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11143
    = surrogateDiagTailX0RatChunk000Sub001Block069Part017

theorem surrogateDiagonalTailChunk000Sub001Block069Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part017] using hcert

def TailChunk000Sub001Block069Part018SupportExplicit : Finset ℕ :=
  ([11145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part018 : ℚ :=
  (1257054841325 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk000Sub001Block069Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11145
    = surrogateDiagTailX0RatChunk000Sub001Block069Part018

theorem surrogateDiagonalTailChunk000Sub001Block069Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part018] using hcert

def TailChunk000Sub001Block069Part019SupportExplicit : Finset ℕ :=
  ([11146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part019 : ℚ :=
  (485286390625 : ℚ) / 602575262410451232

def SurrogateDiagonalTailChunk000Sub001Block069Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11146
    = surrogateDiagTailX0RatChunk000Sub001Block069Part019

theorem surrogateDiagonalTailChunk000Sub001Block069Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part019] using hcert

def TailChunk000Sub001Block069Part020SupportExplicit : Finset ℕ :=
  ([11147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part020 : ℚ :=
  (859716503 : ℚ) / 4063585101069312

def SurrogateDiagonalTailChunk000Sub001Block069Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11147
    = surrogateDiagTailX0RatChunk000Sub001Block069Part020

theorem surrogateDiagonalTailChunk000Sub001Block069Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part020] using hcert

def TailChunk000Sub001Block069Part021SupportExplicit : Finset ℕ :=
  ([11149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part021 : ℚ :=
  (1942190640625 : ℚ) / 9655054013823589152

def SurrogateDiagonalTailChunk000Sub001Block069Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11149
    = surrogateDiagTailX0RatChunk000Sub001Block069Part021

theorem surrogateDiagonalTailChunk000Sub001Block069Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part021] using hcert

def TailChunk000Sub001Block069Part022SupportExplicit : Finset ℕ :=
  ([11153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part022 : ℚ :=
  (2377354346725 : ℚ) / 10317775847684708736

def SurrogateDiagonalTailChunk000Sub001Block069Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11153
    = surrogateDiagTailX0RatChunk000Sub001Block069Part022

theorem surrogateDiagonalTailChunk000Sub001Block069Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part022] using hcert

def TailChunk000Sub001Block069Part023SupportExplicit : Finset ℕ :=
  ([11155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part023 : ℚ :=
  (4882201063225 : ℚ) / 12736276522554359808

def SurrogateDiagonalTailChunk000Sub001Block069Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11155
    = surrogateDiagTailX0RatChunk000Sub001Block069Part023

theorem surrogateDiagonalTailChunk000Sub001Block069Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part023] using hcert

def TailChunk000Sub001Block069Part024SupportExplicit : Finset ℕ :=
  ([11157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block069Part024 : ℚ :=
  (314227784375 : ℚ) / 695011031788115328

def SurrogateDiagonalTailChunk000Sub001Block069Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11157
    = surrogateDiagTailX0RatChunk000Sub001Block069Part024

theorem surrogateDiagonalTailChunk000Sub001Block069Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block069Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block069Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block069Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block069Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block069Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block069HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block069Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block069Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block069Part000
    + surrogateDiagTailX0RatChunk000Sub001Block069Part001
    + surrogateDiagTailX0RatChunk000Sub001Block069Part002
    + surrogateDiagTailX0RatChunk000Sub001Block069Part003
    + surrogateDiagTailX0RatChunk000Sub001Block069Part004
    + surrogateDiagTailX0RatChunk000Sub001Block069Part005
    + surrogateDiagTailX0RatChunk000Sub001Block069Part006
    + surrogateDiagTailX0RatChunk000Sub001Block069Part007
    + surrogateDiagTailX0RatChunk000Sub001Block069Part008
    + surrogateDiagTailX0RatChunk000Sub001Block069Part009

def surrogateDiagonalTailChunk000Sub001Block069MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block069Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block069Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block069Part010
    + surrogateDiagTailX0RatChunk000Sub001Block069Part011
    + surrogateDiagTailX0RatChunk000Sub001Block069Part012
    + surrogateDiagTailX0RatChunk000Sub001Block069Part013
    + surrogateDiagTailX0RatChunk000Sub001Block069Part014
    + surrogateDiagTailX0RatChunk000Sub001Block069Part015
    + surrogateDiagTailX0RatChunk000Sub001Block069Part016
    + surrogateDiagTailX0RatChunk000Sub001Block069Part017
    + surrogateDiagTailX0RatChunk000Sub001Block069Part018
    + surrogateDiagTailX0RatChunk000Sub001Block069Part019

def surrogateDiagonalTailChunk000Sub001Block069TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block069Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block069Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block069Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block069Part020
    + surrogateDiagTailX0RatChunk000Sub001Block069Part021
    + surrogateDiagTailX0RatChunk000Sub001Block069Part022
    + surrogateDiagTailX0RatChunk000Sub001Block069Part023
    + surrogateDiagTailX0RatChunk000Sub001Block069Part024

def surrogateDiagonalTailChunk000Sub001Block069Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block069HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block069MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block069TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block069 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block069Part000
    + surrogateDiagTailX0RatChunk000Sub001Block069Part001
    + surrogateDiagTailX0RatChunk000Sub001Block069Part002
    + surrogateDiagTailX0RatChunk000Sub001Block069Part003
    + surrogateDiagTailX0RatChunk000Sub001Block069Part004
    + surrogateDiagTailX0RatChunk000Sub001Block069Part005
    + surrogateDiagTailX0RatChunk000Sub001Block069Part006
    + surrogateDiagTailX0RatChunk000Sub001Block069Part007
    + surrogateDiagTailX0RatChunk000Sub001Block069Part008
    + surrogateDiagTailX0RatChunk000Sub001Block069Part009
    + surrogateDiagTailX0RatChunk000Sub001Block069Part010
    + surrogateDiagTailX0RatChunk000Sub001Block069Part011
    + surrogateDiagTailX0RatChunk000Sub001Block069Part012
    + surrogateDiagTailX0RatChunk000Sub001Block069Part013
    + surrogateDiagTailX0RatChunk000Sub001Block069Part014
    + surrogateDiagTailX0RatChunk000Sub001Block069Part015
    + surrogateDiagTailX0RatChunk000Sub001Block069Part016
    + surrogateDiagTailX0RatChunk000Sub001Block069Part017
    + surrogateDiagTailX0RatChunk000Sub001Block069Part018
    + surrogateDiagTailX0RatChunk000Sub001Block069Part019
    + surrogateDiagTailX0RatChunk000Sub001Block069Part020
    + surrogateDiagTailX0RatChunk000Sub001Block069Part021
    + surrogateDiagTailX0RatChunk000Sub001Block069Part022
    + surrogateDiagTailX0RatChunk000Sub001Block069Part023
    + surrogateDiagTailX0RatChunk000Sub001Block069Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block069_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block069Head + surrogateDiagTailX0RatChunk000Sub001Block069Mid + surrogateDiagTailX0RatChunk000Sub001Block069Tail =
      surrogateDiagTailX0RatChunk000Sub001Block069 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block069Head surrogateDiagTailX0RatChunk000Sub001Block069Mid surrogateDiagTailX0RatChunk000Sub001Block069Tail surrogateDiagTailX0RatChunk000Sub001Block069
  ring

def SurrogateDiagonalTailChunk000Sub001Block069HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block069HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block069Head

def SurrogateDiagonalTailChunk000Sub001Block069MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block069MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block069Mid

def SurrogateDiagonalTailChunk000Sub001Block069TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block069TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block069Tail

theorem surrogateDiagonalTailChunk000Sub001Block069_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block069HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block069MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block069TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block069Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block069 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block069HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block069MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block069TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block069Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block069_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
