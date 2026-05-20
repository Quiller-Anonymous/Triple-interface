import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [88,89). -/

/- Block 088 covers tail-support indices [2200,2225) and q from 3667 to 3707. -/

def TailChunk000Sub000Block088Part000SupportExplicit : Finset ℕ :=
  ([3667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part000 : ℚ :=
  (117163675 : ℚ) / 51608123080704

def SurrogateDiagonalTailChunk000Sub000Block088Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3667
    = surrogateDiagTailX0RatChunk000Sub000Block088Part000

theorem surrogateDiagonalTailChunk000Sub000Block088Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part000] using hcert

def TailChunk000Sub000Block088Part001SupportExplicit : Finset ℕ :=
  ([3669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part001 : ℚ :=
  (654048528175 : ℚ) / 89213723363077248

def SurrogateDiagonalTailChunk000Sub000Block088Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3669
    = surrogateDiagTailX0RatChunk000Sub000Block088Part001

theorem surrogateDiagonalTailChunk000Sub000Block088Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part001] using hcert

def TailChunk000Sub000Block088Part002SupportExplicit : Finset ℕ :=
  ([3670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part002 : ℚ :=
  (20637810725 : ℚ) / 478607967412992

def SurrogateDiagonalTailChunk000Sub000Block088Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3670
    = surrogateDiagTailX0RatChunk000Sub000Block088Part002

theorem surrogateDiagonalTailChunk000Sub000Block088Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part002] using hcert

def TailChunk000Sub000Block088Part003SupportExplicit : Finset ℕ :=
  ([3671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part003 : ℚ :=
  (336906025 : ℚ) / 181447549463442

def SurrogateDiagonalTailChunk000Sub000Block088Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3671
    = surrogateDiagTailX0RatChunk000Sub000Block088Part003

theorem surrogateDiagonalTailChunk000Sub000Block088Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part003] using hcert

def TailChunk000Sub000Block088Part004SupportExplicit : Finset ℕ :=
  ([3673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part004 : ℚ :=
  (210795765625 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub000Block088Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3673
    = surrogateDiagTailX0RatChunk000Sub000Block088Part004

theorem surrogateDiagonalTailChunk000Sub000Block088Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part004] using hcert

def TailChunk000Sub000Block088Part005SupportExplicit : Finset ℕ :=
  ([3674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part005 : ℚ :=
  (5255014017 : ℚ) / 253161667542400

def SurrogateDiagonalTailChunk000Sub000Block088Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3674
    = surrogateDiagTailX0RatChunk000Sub000Block088Part005

theorem surrogateDiagonalTailChunk000Sub000Block088Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part005] using hcert

def TailChunk000Sub000Block088Part006SupportExplicit : Finset ℕ :=
  ([3677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part006 : ℚ :=
  (1689703116775 : ℚ) / 456592601201628288

def SurrogateDiagonalTailChunk000Sub000Block088Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3677
    = surrogateDiagTailX0RatChunk000Sub000Block088Part006

theorem surrogateDiagonalTailChunk000Sub000Block088Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part006] using hcert

def TailChunk000Sub000Block088Part007SupportExplicit : Finset ℕ :=
  ([3678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part007 : ℚ :=
  (732816325 : ℚ) / 10317004748352

def SurrogateDiagonalTailChunk000Sub000Block088Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3678
    = surrogateDiagTailX0RatChunk000Sub000Block088Part007

theorem surrogateDiagonalTailChunk000Sub000Block088Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part007] using hcert

def TailChunk000Sub000Block088Part008SupportExplicit : Finset ℕ :=
  ([3679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part008 : ℚ :=
  (378732398275 : ℚ) / 81976294805524992

def SurrogateDiagonalTailChunk000Sub000Block088Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3679
    = surrogateDiagTailX0RatChunk000Sub000Block088Part008

theorem surrogateDiagonalTailChunk000Sub000Block088Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part008] using hcert

def TailChunk000Sub000Block088Part009SupportExplicit : Finset ℕ :=
  ([3682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part009 : ℚ :=
  (533960961025 : ℚ) / 15269929279820928

def SurrogateDiagonalTailChunk000Sub000Block088Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3682
    = surrogateDiagTailX0RatChunk000Sub000Block088Part009

theorem surrogateDiagonalTailChunk000Sub000Block088Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part009] using hcert

def TailChunk000Sub000Block088Part010SupportExplicit : Finset ℕ :=
  ([3683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part010 : ℚ :=
  (400359354925 : ℚ) / 96845885268152832

def SurrogateDiagonalTailChunk000Sub000Block088Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3683
    = surrogateDiagTailX0RatChunk000Sub000Block088Part010

theorem surrogateDiagonalTailChunk000Sub000Block088Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part010] using hcert

def TailChunk000Sub000Block088Part011SupportExplicit : Finset ℕ :=
  ([3685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part011 : ℚ :=
  (21826964459 : ℚ) / 2429251961241600

def SurrogateDiagonalTailChunk000Sub000Block088Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3685
    = surrogateDiagTailX0RatChunk000Sub000Block088Part011

theorem surrogateDiagonalTailChunk000Sub000Block088Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part011] using hcert

def TailChunk000Sub000Block088Part012SupportExplicit : Finset ℕ :=
  ([3686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part012 : ℚ :=
  (16493605675 : ℚ) / 619297476968448

def SurrogateDiagonalTailChunk000Sub000Block088Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3686
    = surrogateDiagTailX0RatChunk000Sub000Block088Part012

theorem surrogateDiagonalTailChunk000Sub000Block088Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part012] using hcert

def TailChunk000Sub000Block088Part013SupportExplicit : Finset ℕ :=
  ([3687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part013 : ℚ :=
  (660480880525 : ℚ) / 90978821896194048

def SurrogateDiagonalTailChunk000Sub000Block088Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3687
    = surrogateDiagTailX0RatChunk000Sub000Block088Part013

theorem surrogateDiagonalTailChunk000Sub000Block088Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part013] using hcert

def TailChunk000Sub000Block088Part014SupportExplicit : Finset ℕ :=
  ([3689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part014 : ℚ :=
  (360064847 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block088Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3689
    = surrogateDiagTailX0RatChunk000Sub000Block088Part014

theorem surrogateDiagonalTailChunk000Sub000Block088Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part014] using hcert

def TailChunk000Sub000Block088Part015SupportExplicit : Finset ℕ :=
  ([3691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part015 : ℚ :=
  (340587025 : ℚ) / 185435258845842

def SurrogateDiagonalTailChunk000Sub000Block088Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3691
    = surrogateDiagTailX0RatChunk000Sub000Block088Part015

theorem surrogateDiagonalTailChunk000Sub000Block088Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part015] using hcert

def TailChunk000Sub000Block088Part016SupportExplicit : Finset ℕ :=
  ([3693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part016 : ℚ :=
  (26505279967 : ℚ) / 3662918693251200

def SurrogateDiagonalTailChunk000Sub000Block088Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3693
    = surrogateDiagTailX0RatChunk000Sub000Block088Part016

theorem surrogateDiagonalTailChunk000Sub000Block088Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part016] using hcert

def TailChunk000Sub000Block088Part017SupportExplicit : Finset ℕ :=
  ([3694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part017 : ℚ :=
  (213127777275 : ℚ) / 9679042368602776

def SurrogateDiagonalTailChunk000Sub000Block088Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3694
    = surrogateDiagTailX0RatChunk000Sub000Block088Part017

theorem surrogateDiagonalTailChunk000Sub000Block088Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part017] using hcert

def TailChunk000Sub000Block088Part018SupportExplicit : Finset ℕ :=
  ([3695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part018 : ℚ :=
  (250085899325 : ℚ) / 63295235019380736

def SurrogateDiagonalTailChunk000Sub000Block088Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3695
    = surrogateDiagTailX0RatChunk000Sub000Block088Part018

theorem surrogateDiagonalTailChunk000Sub000Block088Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part018] using hcert

def TailChunk000Sub000Block088Part019SupportExplicit : Finset ℕ :=
  ([3697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part019 : ℚ :=
  (213559515625 : ℚ) / 116652679178821632

def SurrogateDiagonalTailChunk000Sub000Block088Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3697
    = surrogateDiagTailX0RatChunk000Sub000Block088Part019

theorem surrogateDiagonalTailChunk000Sub000Block088Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part019] using hcert

def TailChunk000Sub000Block088Part020SupportExplicit : Finset ℕ :=
  ([3701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part020 : ℚ :=
  (13697401 : ℚ) / 7498143328800

def SurrogateDiagonalTailChunk000Sub000Block088Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3701
    = surrogateDiagTailX0RatChunk000Sub000Block088Part020

theorem surrogateDiagonalTailChunk000Sub000Block088Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part020] using hcert

def TailChunk000Sub000Block088Part021SupportExplicit : Finset ℕ :=
  ([3702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part021 : ℚ :=
  (2970497725 : ℚ) / 51434161895424

def SurrogateDiagonalTailChunk000Sub000Block088Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3702
    = surrogateDiagTailX0RatChunk000Sub000Block088Part021

theorem surrogateDiagonalTailChunk000Sub000Block088Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part021] using hcert

def TailChunk000Sub000Block088Part022SupportExplicit : Finset ℕ :=
  ([3705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part022 : ℚ :=
  (311505088925 : ℚ) / 11147354585432064

def SurrogateDiagonalTailChunk000Sub000Block088Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3705
    = surrogateDiagTailX0RatChunk000Sub000Block088Part022

theorem surrogateDiagonalTailChunk000Sub000Block088Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part022] using hcert

def TailChunk000Sub000Block088Part023SupportExplicit : Finset ℕ :=
  ([3706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part023 : ℚ :=
  (149070494875 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block088Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3706
    = surrogateDiagTailX0RatChunk000Sub000Block088Part023

theorem surrogateDiagonalTailChunk000Sub000Block088Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part023] using hcert

def TailChunk000Sub000Block088Part024SupportExplicit : Finset ℕ :=
  ([3707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block088Part024 : ℚ :=
  (1673638273 : ℚ) / 354112664371200

def SurrogateDiagonalTailChunk000Sub000Block088Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3707
    = surrogateDiagTailX0RatChunk000Sub000Block088Part024

theorem surrogateDiagonalTailChunk000Sub000Block088Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block088Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block088Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block088Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block088Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block088Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block088HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block088Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block088Part000
    + surrogateDiagTailX0RatChunk000Sub000Block088Part001
    + surrogateDiagTailX0RatChunk000Sub000Block088Part002
    + surrogateDiagTailX0RatChunk000Sub000Block088Part003
    + surrogateDiagTailX0RatChunk000Sub000Block088Part004
    + surrogateDiagTailX0RatChunk000Sub000Block088Part005
    + surrogateDiagTailX0RatChunk000Sub000Block088Part006
    + surrogateDiagTailX0RatChunk000Sub000Block088Part007
    + surrogateDiagTailX0RatChunk000Sub000Block088Part008
    + surrogateDiagTailX0RatChunk000Sub000Block088Part009

def surrogateDiagonalTailChunk000Sub000Block088MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block088Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block088Part010
    + surrogateDiagTailX0RatChunk000Sub000Block088Part011
    + surrogateDiagTailX0RatChunk000Sub000Block088Part012
    + surrogateDiagTailX0RatChunk000Sub000Block088Part013
    + surrogateDiagTailX0RatChunk000Sub000Block088Part014
    + surrogateDiagTailX0RatChunk000Sub000Block088Part015
    + surrogateDiagTailX0RatChunk000Sub000Block088Part016
    + surrogateDiagTailX0RatChunk000Sub000Block088Part017
    + surrogateDiagTailX0RatChunk000Sub000Block088Part018
    + surrogateDiagTailX0RatChunk000Sub000Block088Part019

def surrogateDiagonalTailChunk000Sub000Block088TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block088Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block088Part020
    + surrogateDiagTailX0RatChunk000Sub000Block088Part021
    + surrogateDiagTailX0RatChunk000Sub000Block088Part022
    + surrogateDiagTailX0RatChunk000Sub000Block088Part023
    + surrogateDiagTailX0RatChunk000Sub000Block088Part024

def surrogateDiagonalTailChunk000Sub000Block088Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block088HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block088MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block088TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block088 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block088Part000
    + surrogateDiagTailX0RatChunk000Sub000Block088Part001
    + surrogateDiagTailX0RatChunk000Sub000Block088Part002
    + surrogateDiagTailX0RatChunk000Sub000Block088Part003
    + surrogateDiagTailX0RatChunk000Sub000Block088Part004
    + surrogateDiagTailX0RatChunk000Sub000Block088Part005
    + surrogateDiagTailX0RatChunk000Sub000Block088Part006
    + surrogateDiagTailX0RatChunk000Sub000Block088Part007
    + surrogateDiagTailX0RatChunk000Sub000Block088Part008
    + surrogateDiagTailX0RatChunk000Sub000Block088Part009
    + surrogateDiagTailX0RatChunk000Sub000Block088Part010
    + surrogateDiagTailX0RatChunk000Sub000Block088Part011
    + surrogateDiagTailX0RatChunk000Sub000Block088Part012
    + surrogateDiagTailX0RatChunk000Sub000Block088Part013
    + surrogateDiagTailX0RatChunk000Sub000Block088Part014
    + surrogateDiagTailX0RatChunk000Sub000Block088Part015
    + surrogateDiagTailX0RatChunk000Sub000Block088Part016
    + surrogateDiagTailX0RatChunk000Sub000Block088Part017
    + surrogateDiagTailX0RatChunk000Sub000Block088Part018
    + surrogateDiagTailX0RatChunk000Sub000Block088Part019
    + surrogateDiagTailX0RatChunk000Sub000Block088Part020
    + surrogateDiagTailX0RatChunk000Sub000Block088Part021
    + surrogateDiagTailX0RatChunk000Sub000Block088Part022
    + surrogateDiagTailX0RatChunk000Sub000Block088Part023
    + surrogateDiagTailX0RatChunk000Sub000Block088Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block088_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block088Head + surrogateDiagTailX0RatChunk000Sub000Block088Mid + surrogateDiagTailX0RatChunk000Sub000Block088Tail =
      surrogateDiagTailX0RatChunk000Sub000Block088 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block088Head surrogateDiagTailX0RatChunk000Sub000Block088Mid surrogateDiagTailX0RatChunk000Sub000Block088Tail surrogateDiagTailX0RatChunk000Sub000Block088
  ring

def SurrogateDiagonalTailChunk000Sub000Block088HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block088HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block088Head

def SurrogateDiagonalTailChunk000Sub000Block088MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block088MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block088Mid

def SurrogateDiagonalTailChunk000Sub000Block088TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block088TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block088Tail

theorem surrogateDiagonalTailChunk000Sub000Block088_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block088HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block088MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block088TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block088Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block088 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block088HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block088MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block088TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block088Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block088_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
