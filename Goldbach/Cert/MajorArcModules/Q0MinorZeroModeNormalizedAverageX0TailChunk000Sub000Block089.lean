import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [89,90). -/

/- Block 089 covers tail-support indices [2225,2250) and q from 3709 to 3749. -/

def TailChunk000Sub000Block089Part000SupportExplicit : Finset ℕ :=
  ([3709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part000 : ℚ :=
  (1719241207975 : ℚ) / 472700172484510848

def SurrogateDiagonalTailChunk000Sub000Block089Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3709
    = surrogateDiagTailX0RatChunk000Sub000Block089Part000

theorem surrogateDiagonalTailChunk000Sub000Block089Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part000] using hcert

def TailChunk000Sub000Block089Part001SupportExplicit : Finset ℕ :=
  ([3710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part001 : ℚ :=
  (210319834325 : ℚ) / 3032879842197504

def SurrogateDiagonalTailChunk000Sub000Block089Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3710
    = surrogateDiagTailX0RatChunk000Sub000Block089Part001

theorem surrogateDiagonalTailChunk000Sub000Block089Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part001] using hcert

def TailChunk000Sub000Block089Part002SupportExplicit : Finset ℕ :=
  ([3711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part002 : ℚ :=
  (477774539225 : ℚ) / 46686436788593664

def SurrogateDiagonalTailChunk000Sub000Block089Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3711
    = surrogateDiagTailX0RatChunk000Sub000Block089Part002

theorem surrogateDiagonalTailChunk000Sub000Block089Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part002] using hcert

def TailChunk000Sub000Block089Part003SupportExplicit : Finset ℕ :=
  ([3713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part003 : ℚ :=
  (1646722531075 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk000Sub000Block089Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3713
    = surrogateDiagTailX0RatChunk000Sub000Block089Part003

theorem surrogateDiagonalTailChunk000Sub000Block089Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part003] using hcert

def TailChunk000Sub000Block089Part004SupportExplicit : Finset ℕ :=
  ([3714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part004 : ℚ :=
  (83713888375 : ℚ) / 1458951149643552

def SurrogateDiagonalTailChunk000Sub000Block089Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3714
    = surrogateDiagTailX0RatChunk000Sub000Block089Part004

theorem surrogateDiagonalTailChunk000Sub000Block089Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part004] using hcert

def TailChunk000Sub000Block089Part005SupportExplicit : Finset ℕ :=
  ([3715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part005 : ℚ :=
  (758399028775 : ℚ) / 194036059033356288

def SurrogateDiagonalTailChunk000Sub000Block089Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3715
    = surrogateDiagTailX0RatChunk000Sub000Block089Part005

theorem surrogateDiagonalTailChunk000Sub000Block089Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part005] using hcert

def TailChunk000Sub000Block089Part006SupportExplicit : Finset ℕ :=
  ([3719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part006 : ℚ :=
  (216108765625 : ℚ) / 119455021088582322

def SurrogateDiagonalTailChunk000Sub000Block089Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3719
    = surrogateDiagTailX0RatChunk000Sub000Block089Part006

theorem surrogateDiagonalTailChunk000Sub000Block089Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part006] using hcert

def TailChunk000Sub000Block089Part007SupportExplicit : Finset ℕ :=
  ([3722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part007 : ℚ :=
  (2884946393 : ℚ) / 133013621404800

def SurrogateDiagonalTailChunk000Sub000Block089Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3722
    = surrogateDiagTailX0RatChunk000Sub000Block089Part007

theorem surrogateDiagonalTailChunk000Sub000Block089Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part007] using hcert

def TailChunk000Sub000Block089Part008SupportExplicit : Finset ℕ :=
  ([3723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part008 : ℚ :=
  (210581258725 : ℚ) / 23487430237618176

def SurrogateDiagonalTailChunk000Sub000Block089Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3723
    = surrogateDiagTailX0RatChunk000Sub000Block089Part008

theorem surrogateDiagonalTailChunk000Sub000Block089Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part008] using hcert

def TailChunk000Sub000Block089Part009SupportExplicit : Finset ℕ :=
  ([3727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part009 : ℚ :=
  (217039515625 : ℚ) / 120486466988512722

def SurrogateDiagonalTailChunk000Sub000Block089Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3727
    = surrogateDiagTailX0RatChunk000Sub000Block089Part009

theorem surrogateDiagonalTailChunk000Sub000Block089Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part009] using hcert

def TailChunk000Sub000Block089Part010SupportExplicit : Finset ℕ :=
  ([3729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part010 : ℚ :=
  (4134595737 : ℚ) / 419689083699200

def SurrogateDiagonalTailChunk000Sub000Block089Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3729
    = surrogateDiagTailX0RatChunk000Sub000Block089Part010

theorem surrogateDiagonalTailChunk000Sub000Block089Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part010] using hcert

def TailChunk000Sub000Block089Part011SupportExplicit : Finset ℕ :=
  ([3730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part011 : ℚ :=
  (186607089725 : ℚ) / 6129267674333184

def SurrogateDiagonalTailChunk000Sub000Block089Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3730
    = surrogateDiagTailX0RatChunk000Sub000Block089Part011

theorem surrogateDiagonalTailChunk000Sub000Block089Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part011] using hcert

def TailChunk000Sub000Block089Part012SupportExplicit : Finset ℕ :=
  ([3731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part012 : ℚ :=
  (14462308199 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block089Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3731
    = surrogateDiagTailX0RatChunk000Sub000Block089Part012

theorem surrogateDiagonalTailChunk000Sub000Block089Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part012] using hcert

def TailChunk000Sub000Block089Part013SupportExplicit : Finset ℕ :=
  ([3733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part013 : ℚ :=
  (1741562742775 : ℚ) / 485057695578127488

def SurrogateDiagonalTailChunk000Sub000Block089Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3733
    = surrogateDiagTailX0RatChunk000Sub000Block089Part013

theorem surrogateDiagonalTailChunk000Sub000Block089Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part013] using hcert

def TailChunk000Sub000Block089Part014SupportExplicit : Finset ℕ :=
  ([3734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part014 : ℚ :=
  (72589473425 : ℚ) / 3368456219292552

def SurrogateDiagonalTailChunk000Sub000Block089Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3734
    = surrogateDiagTailX0RatChunk000Sub000Block089Part014

theorem surrogateDiagonalTailChunk000Sub000Block089Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part014] using hcert

def TailChunk000Sub000Block089Part015SupportExplicit : Finset ℕ :=
  ([3737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part015 : ℚ :=
  (7383700127 : ℚ) / 1866613248000000

def SurrogateDiagonalTailChunk000Sub000Block089Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3737
    = surrogateDiagTailX0RatChunk000Sub000Block089Part015

theorem surrogateDiagonalTailChunk000Sub000Block089Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part015] using hcert

def TailChunk000Sub000Block089Part016SupportExplicit : Finset ℕ :=
  ([3738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part016 : ℚ :=
  (43365635375 : ℚ) / 388680313798656

def SurrogateDiagonalTailChunk000Sub000Block089Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3738
    = surrogateDiagTailX0RatChunk000Sub000Block089Part016

theorem surrogateDiagonalTailChunk000Sub000Block089Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part016] using hcert

def TailChunk000Sub000Block089Part017SupportExplicit : Finset ℕ :=
  ([3739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part017 : ℚ :=
  (1747165621975 : ℚ) / 488184568267015368

def SurrogateDiagonalTailChunk000Sub000Block089Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3739
    = surrogateDiagTailX0RatChunk000Sub000Block089Part017

theorem surrogateDiagonalTailChunk000Sub000Block089Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part017] using hcert

def TailChunk000Sub000Block089Part018SupportExplicit : Finset ℕ :=
  ([3741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part018 : ℚ :=
  (4494743975 : ℚ) / 531390316972032

def SurrogateDiagonalTailChunk000Sub000Block089Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3741
    = surrogateDiagTailX0RatChunk000Sub000Block089Part018

theorem surrogateDiagonalTailChunk000Sub000Block089Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part018] using hcert

def TailChunk000Sub000Block089Part019SupportExplicit : Finset ℕ :=
  ([3742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part019 : ℚ :=
  (17499704359 : ℚ) / 1223075527192200

def SurrogateDiagonalTailChunk000Sub000Block089Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3742
    = surrogateDiagTailX0RatChunk000Sub000Block089Part019

theorem surrogateDiagonalTailChunk000Sub000Block089Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part019] using hcert

def TailChunk000Sub000Block089Part020SupportExplicit : Finset ℕ :=
  ([3743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part020 : ℚ :=
  (841299008575 : ℚ) / 387383541072611328

def SurrogateDiagonalTailChunk000Sub000Block089Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3743
    = surrogateDiagTailX0RatChunk000Sub000Block089Part020

theorem surrogateDiagonalTailChunk000Sub000Block089Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part020] using hcert

def TailChunk000Sub000Block089Part021SupportExplicit : Finset ℕ :=
  ([3745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part021 : ℚ :=
  (9390306325 : ℚ) / 1454664332611584

def SurrogateDiagonalTailChunk000Sub000Block089Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3745
    = surrogateDiagTailX0RatChunk000Sub000Block089Part021

theorem surrogateDiagonalTailChunk000Sub000Block089Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part021] using hcert

def TailChunk000Sub000Block089Part022SupportExplicit : Finset ℕ :=
  ([3746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part022 : ℚ :=
  (73056786425 : ℚ) / 3411989822472192

def SurrogateDiagonalTailChunk000Sub000Block089Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3746
    = surrogateDiagTailX0RatChunk000Sub000Block089Part022

theorem surrogateDiagonalTailChunk000Sub000Block089Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part022] using hcert

def TailChunk000Sub000Block089Part023SupportExplicit : Finset ℕ :=
  ([3747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part023 : ℚ :=
  (682149594025 : ℚ) / 97052154950320128

def SurrogateDiagonalTailChunk000Sub000Block089Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3747
    = surrogateDiagTailX0RatChunk000Sub000Block089Part023

theorem surrogateDiagonalTailChunk000Sub000Block089Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part023] using hcert

def TailChunk000Sub000Block089Part024SupportExplicit : Finset ℕ :=
  ([3749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block089Part024 : ℚ :=
  (850068678475 : ℚ) / 403438778604436608

def SurrogateDiagonalTailChunk000Sub000Block089Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3749
    = surrogateDiagTailX0RatChunk000Sub000Block089Part024

theorem surrogateDiagonalTailChunk000Sub000Block089Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block089Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block089Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block089Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block089Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block089Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block089HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block089Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block089Part000
    + surrogateDiagTailX0RatChunk000Sub000Block089Part001
    + surrogateDiagTailX0RatChunk000Sub000Block089Part002
    + surrogateDiagTailX0RatChunk000Sub000Block089Part003
    + surrogateDiagTailX0RatChunk000Sub000Block089Part004
    + surrogateDiagTailX0RatChunk000Sub000Block089Part005
    + surrogateDiagTailX0RatChunk000Sub000Block089Part006
    + surrogateDiagTailX0RatChunk000Sub000Block089Part007
    + surrogateDiagTailX0RatChunk000Sub000Block089Part008
    + surrogateDiagTailX0RatChunk000Sub000Block089Part009

def surrogateDiagonalTailChunk000Sub000Block089MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block089Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block089Part010
    + surrogateDiagTailX0RatChunk000Sub000Block089Part011
    + surrogateDiagTailX0RatChunk000Sub000Block089Part012
    + surrogateDiagTailX0RatChunk000Sub000Block089Part013
    + surrogateDiagTailX0RatChunk000Sub000Block089Part014
    + surrogateDiagTailX0RatChunk000Sub000Block089Part015
    + surrogateDiagTailX0RatChunk000Sub000Block089Part016
    + surrogateDiagTailX0RatChunk000Sub000Block089Part017
    + surrogateDiagTailX0RatChunk000Sub000Block089Part018
    + surrogateDiagTailX0RatChunk000Sub000Block089Part019

def surrogateDiagonalTailChunk000Sub000Block089TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block089Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block089Part020
    + surrogateDiagTailX0RatChunk000Sub000Block089Part021
    + surrogateDiagTailX0RatChunk000Sub000Block089Part022
    + surrogateDiagTailX0RatChunk000Sub000Block089Part023
    + surrogateDiagTailX0RatChunk000Sub000Block089Part024

def surrogateDiagonalTailChunk000Sub000Block089Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block089HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block089MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block089TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block089 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block089Part000
    + surrogateDiagTailX0RatChunk000Sub000Block089Part001
    + surrogateDiagTailX0RatChunk000Sub000Block089Part002
    + surrogateDiagTailX0RatChunk000Sub000Block089Part003
    + surrogateDiagTailX0RatChunk000Sub000Block089Part004
    + surrogateDiagTailX0RatChunk000Sub000Block089Part005
    + surrogateDiagTailX0RatChunk000Sub000Block089Part006
    + surrogateDiagTailX0RatChunk000Sub000Block089Part007
    + surrogateDiagTailX0RatChunk000Sub000Block089Part008
    + surrogateDiagTailX0RatChunk000Sub000Block089Part009
    + surrogateDiagTailX0RatChunk000Sub000Block089Part010
    + surrogateDiagTailX0RatChunk000Sub000Block089Part011
    + surrogateDiagTailX0RatChunk000Sub000Block089Part012
    + surrogateDiagTailX0RatChunk000Sub000Block089Part013
    + surrogateDiagTailX0RatChunk000Sub000Block089Part014
    + surrogateDiagTailX0RatChunk000Sub000Block089Part015
    + surrogateDiagTailX0RatChunk000Sub000Block089Part016
    + surrogateDiagTailX0RatChunk000Sub000Block089Part017
    + surrogateDiagTailX0RatChunk000Sub000Block089Part018
    + surrogateDiagTailX0RatChunk000Sub000Block089Part019
    + surrogateDiagTailX0RatChunk000Sub000Block089Part020
    + surrogateDiagTailX0RatChunk000Sub000Block089Part021
    + surrogateDiagTailX0RatChunk000Sub000Block089Part022
    + surrogateDiagTailX0RatChunk000Sub000Block089Part023
    + surrogateDiagTailX0RatChunk000Sub000Block089Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block089_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block089Head + surrogateDiagTailX0RatChunk000Sub000Block089Mid + surrogateDiagTailX0RatChunk000Sub000Block089Tail =
      surrogateDiagTailX0RatChunk000Sub000Block089 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block089Head surrogateDiagTailX0RatChunk000Sub000Block089Mid surrogateDiagTailX0RatChunk000Sub000Block089Tail surrogateDiagTailX0RatChunk000Sub000Block089
  ring

def SurrogateDiagonalTailChunk000Sub000Block089HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block089HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block089Head

def SurrogateDiagonalTailChunk000Sub000Block089MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block089MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block089Mid

def SurrogateDiagonalTailChunk000Sub000Block089TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block089TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block089Tail

theorem surrogateDiagonalTailChunk000Sub000Block089_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block089HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block089MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block089TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block089Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block089 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block089HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block089MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block089TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block089Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block089_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
