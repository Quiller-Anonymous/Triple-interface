import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [87,88). -/

/- Block 087 covers tail-support indices [2175,2200) and q from 3623 to 3666. -/

def TailChunk000Sub000Block087Part000SupportExplicit : Finset ℕ :=
  ([3623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part000 : ℚ :=
  (205095765625 : ℚ) / 107587211518085682

def SurrogateDiagonalTailChunk000Sub000Block087Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3623
    = surrogateDiagTailX0RatChunk000Sub000Block087Part000

theorem surrogateDiagonalTailChunk000Sub000Block087Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part000] using hcert

def TailChunk000Sub000Block087Part001SupportExplicit : Finset ℕ :=
  ([3629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part001 : ℚ :=
  (60880733431 : ℚ) / 13683313411459200

def SurrogateDiagonalTailChunk000Sub000Block087Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3629
    = surrogateDiagTailX0RatChunk000Sub000Block087Part001

theorem surrogateDiagonalTailChunk000Sub000Block087Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part001] using hcert

def TailChunk000Sub000Block087Part002SupportExplicit : Finset ℕ :=
  ([3631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part002 : ℚ :=
  (65907620839 : ℚ) / 17366541974872200

def SurrogateDiagonalTailChunk000Sub000Block087Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3631
    = surrogateDiagTailX0RatChunk000Sub000Block087Part002

theorem surrogateDiagonalTailChunk000Sub000Block087Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part002] using hcert

def TailChunk000Sub000Block087Part003SupportExplicit : Finset ℕ :=
  ([3633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part003 : ℚ :=
  (30549207125 : ℚ) / 1680745149333504

def SurrogateDiagonalTailChunk000Sub000Block087Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3633
    = surrogateDiagTailX0RatChunk000Sub000Block087Part003

theorem surrogateDiagonalTailChunk000Sub000Block087Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part003] using hcert

def TailChunk000Sub000Block087Part004SupportExplicit : Finset ℕ :=
  ([3634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part004 : ℚ :=
  (36193962875 : ℚ) / 1971075717756288

def SurrogateDiagonalTailChunk000Sub000Block087Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3634
    = surrogateDiagTailX0RatChunk000Sub000Block087Part004

theorem surrogateDiagonalTailChunk000Sub000Block087Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part004] using hcert

def TailChunk000Sub000Block087Part005SupportExplicit : Finset ℕ :=
  ([3635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part005 : ℚ :=
  (242032582925 : ℚ) / 59277796607563776

def SurrogateDiagonalTailChunk000Sub000Block087Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3635
    = surrogateDiagTailX0RatChunk000Sub000Block087Part005

theorem surrogateDiagonalTailChunk000Sub000Block087Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part005] using hcert

def TailChunk000Sub000Block087Part006SupportExplicit : Finset ℕ :=
  ([3637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part006 : ℚ :=
  (206683890625 : ℚ) / 109260294243070752

def SurrogateDiagonalTailChunk000Sub000Block087Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3637
    = surrogateDiagTailX0RatChunk000Sub000Block087Part006

theorem surrogateDiagonalTailChunk000Sub000Block087Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part006] using hcert

def TailChunk000Sub000Block087Part007SupportExplicit : Finset ℕ :=
  ([3638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part007 : ℚ :=
  (575287150375 : ℚ) / 20688559397142528

def SurrogateDiagonalTailChunk000Sub000Block087Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3638
    = surrogateDiagTailX0RatChunk000Sub000Block087Part007

theorem surrogateDiagonalTailChunk000Sub000Block087Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part007] using hcert

def TailChunk000Sub000Block087Part008SupportExplicit : Finset ℕ :=
  ([3639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part008 : ℚ :=
  (643397952925 : ℚ) / 86329121377241088

def SurrogateDiagonalTailChunk000Sub000Block087Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3639
    = surrogateDiagTailX0RatChunk000Sub000Block087Part008

theorem surrogateDiagonalTailChunk000Sub000Block087Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part008] using hcert

def TailChunk000Sub000Block087Part009SupportExplicit : Finset ℕ :=
  ([3641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part009 : ℚ :=
  (15583340237 : ℚ) / 5930790921000000

def SurrogateDiagonalTailChunk000Sub000Block087Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3641
    = surrogateDiagTailX0RatChunk000Sub000Block087Part009

theorem surrogateDiagonalTailChunk000Sub000Block087Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part009] using hcert

def TailChunk000Sub000Block087Part010SupportExplicit : Finset ℕ :=
  ([3642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part010 : ℚ :=
  (195442934675 : ℚ) / 2697785043038784

def SurrogateDiagonalTailChunk000Sub000Block087Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3642
    = surrogateDiagTailX0RatChunk000Sub000Block087Part010

theorem surrogateDiagonalTailChunk000Sub000Block087Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part010] using hcert

def TailChunk000Sub000Block087Part011SupportExplicit : Finset ℕ :=
  ([3643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part011 : ℚ :=
  (207366390625 : ℚ) / 109983271392637362

def SurrogateDiagonalTailChunk000Sub000Block087Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3643
    = surrogateDiagTailX0RatChunk000Sub000Block087Part011

theorem surrogateDiagonalTailChunk000Sub000Block087Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part011] using hcert

def TailChunk000Sub000Block087Part012SupportExplicit : Finset ℕ :=
  ([3646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part012 : ℚ :=
  (207624979275 : ℚ) / 9185421600189976

def SurrogateDiagonalTailChunk000Sub000Block087Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3646
    = surrogateDiagTailX0RatChunk000Sub000Block087Part012

theorem surrogateDiagonalTailChunk000Sub000Block087Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part012] using hcert

def TailChunk000Sub000Block087Part013SupportExplicit : Finset ℕ :=
  ([3647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part013 : ℚ :=
  (3388860797 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub000Block087Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3647
    = surrogateDiagTailX0RatChunk000Sub000Block087Part013

theorem surrogateDiagonalTailChunk000Sub000Block087Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part013] using hcert

def TailChunk000Sub000Block087Part014SupportExplicit : Finset ℕ :=
  ([3649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part014 : ℚ :=
  (10853904477 : ℚ) / 5118423885414400

def SurrogateDiagonalTailChunk000Sub000Block087Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3649
    = surrogateDiagTailX0RatChunk000Sub000Block087Part014

theorem surrogateDiagonalTailChunk000Sub000Block087Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part014] using hcert

def TailChunk000Sub000Block087Part015SupportExplicit : Finset ℕ :=
  ([3651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part015 : ℚ :=
  (462447701225 : ℚ) / 43737217020985344

def SurrogateDiagonalTailChunk000Sub000Block087Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3651
    = surrogateDiagTailX0RatChunk000Sub000Block087Part015

theorem surrogateDiagonalTailChunk000Sub000Block087Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part015] using hcert

def TailChunk000Sub000Block087Part016SupportExplicit : Finset ℕ :=
  ([3653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part016 : ℚ :=
  (4978567409 : ℚ) / 1062337993113600

def SurrogateDiagonalTailChunk000Sub000Block087Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3653
    = surrogateDiagTailX0RatChunk000Sub000Block087Part016

theorem surrogateDiagonalTailChunk000Sub000Block087Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part016] using hcert

def TailChunk000Sub000Block087Part017SupportExplicit : Finset ℕ :=
  ([3655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part017 : ℚ :=
  (79337494925 : ℚ) / 9324292328128512

def SurrogateDiagonalTailChunk000Sub000Block087Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3655
    = surrogateDiagTailX0RatChunk000Sub000Block087Part017

theorem surrogateDiagonalTailChunk000Sub000Block087Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part017] using hcert

def TailChunk000Sub000Block087Part018SupportExplicit : Finset ℕ :=
  ([3657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part018 : ℚ :=
  (215507851375 : ℚ) / 17131324756795392

def SurrogateDiagonalTailChunk000Sub000Block087Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3657
    = surrogateDiagTailX0RatChunk000Sub000Block087Part018

theorem surrogateDiagonalTailChunk000Sub000Block087Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part018] using hcert

def TailChunk000Sub000Block087Part019SupportExplicit : Finset ℕ :=
  ([3658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part019 : ℚ :=
  (23768651641 : ℚ) / 916819503235200

def SurrogateDiagonalTailChunk000Sub000Block087Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3658
    = surrogateDiagTailX0RatChunk000Sub000Block087Part019

theorem surrogateDiagonalTailChunk000Sub000Block087Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part019] using hcert

def TailChunk000Sub000Block087Part020SupportExplicit : Finset ℕ :=
  ([3659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part020 : ℚ :=
  (1673200417975 : ℚ) / 447715019022024648

def SurrogateDiagonalTailChunk000Sub000Block087Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3659
    = surrogateDiagTailX0RatChunk000Sub000Block087Part020

theorem surrogateDiagonalTailChunk000Sub000Block087Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part020] using hcert

def TailChunk000Sub000Block087Part021SupportExplicit : Finset ℕ :=
  ([3661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part021 : ℚ :=
  (751339329925 : ℚ) / 240610110429045888

def SurrogateDiagonalTailChunk000Sub000Block087Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3661
    = surrogateDiagTailX0RatChunk000Sub000Block087Part021

theorem surrogateDiagonalTailChunk000Sub000Block087Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part021] using hcert

def TailChunk000Sub000Block087Part022SupportExplicit : Finset ℕ :=
  ([3662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part022 : ℚ :=
  (16759452439 : ℚ) / 1121737423624200

def SurrogateDiagonalTailChunk000Sub000Block087Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3662
    = surrogateDiagTailX0RatChunk000Sub000Block087Part022

theorem surrogateDiagonalTailChunk000Sub000Block087Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part022] using hcert

def TailChunk000Sub000Block087Part023SupportExplicit : Finset ℕ :=
  ([3665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part023 : ℚ :=
  (704652801625 : ℚ) / 183785459486588928

def SurrogateDiagonalTailChunk000Sub000Block087Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3665
    = surrogateDiagTailX0RatChunk000Sub000Block087Part023

theorem surrogateDiagonalTailChunk000Sub000Block087Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part023] using hcert

def TailChunk000Sub000Block087Part024SupportExplicit : Finset ℕ :=
  ([3666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block087Part024 : ℚ :=
  (356803156975 : ℚ) / 3714523860860928

def SurrogateDiagonalTailChunk000Sub000Block087Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3666
    = surrogateDiagTailX0RatChunk000Sub000Block087Part024

theorem surrogateDiagonalTailChunk000Sub000Block087Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block087Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block087Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block087Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block087Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block087Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block087HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block087Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block087Part000
    + surrogateDiagTailX0RatChunk000Sub000Block087Part001
    + surrogateDiagTailX0RatChunk000Sub000Block087Part002
    + surrogateDiagTailX0RatChunk000Sub000Block087Part003
    + surrogateDiagTailX0RatChunk000Sub000Block087Part004
    + surrogateDiagTailX0RatChunk000Sub000Block087Part005
    + surrogateDiagTailX0RatChunk000Sub000Block087Part006
    + surrogateDiagTailX0RatChunk000Sub000Block087Part007
    + surrogateDiagTailX0RatChunk000Sub000Block087Part008
    + surrogateDiagTailX0RatChunk000Sub000Block087Part009

def surrogateDiagonalTailChunk000Sub000Block087MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block087Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block087Part010
    + surrogateDiagTailX0RatChunk000Sub000Block087Part011
    + surrogateDiagTailX0RatChunk000Sub000Block087Part012
    + surrogateDiagTailX0RatChunk000Sub000Block087Part013
    + surrogateDiagTailX0RatChunk000Sub000Block087Part014
    + surrogateDiagTailX0RatChunk000Sub000Block087Part015
    + surrogateDiagTailX0RatChunk000Sub000Block087Part016
    + surrogateDiagTailX0RatChunk000Sub000Block087Part017
    + surrogateDiagTailX0RatChunk000Sub000Block087Part018
    + surrogateDiagTailX0RatChunk000Sub000Block087Part019

def surrogateDiagonalTailChunk000Sub000Block087TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block087Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block087Part020
    + surrogateDiagTailX0RatChunk000Sub000Block087Part021
    + surrogateDiagTailX0RatChunk000Sub000Block087Part022
    + surrogateDiagTailX0RatChunk000Sub000Block087Part023
    + surrogateDiagTailX0RatChunk000Sub000Block087Part024

def surrogateDiagonalTailChunk000Sub000Block087Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block087HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block087MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block087TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block087 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block087Part000
    + surrogateDiagTailX0RatChunk000Sub000Block087Part001
    + surrogateDiagTailX0RatChunk000Sub000Block087Part002
    + surrogateDiagTailX0RatChunk000Sub000Block087Part003
    + surrogateDiagTailX0RatChunk000Sub000Block087Part004
    + surrogateDiagTailX0RatChunk000Sub000Block087Part005
    + surrogateDiagTailX0RatChunk000Sub000Block087Part006
    + surrogateDiagTailX0RatChunk000Sub000Block087Part007
    + surrogateDiagTailX0RatChunk000Sub000Block087Part008
    + surrogateDiagTailX0RatChunk000Sub000Block087Part009
    + surrogateDiagTailX0RatChunk000Sub000Block087Part010
    + surrogateDiagTailX0RatChunk000Sub000Block087Part011
    + surrogateDiagTailX0RatChunk000Sub000Block087Part012
    + surrogateDiagTailX0RatChunk000Sub000Block087Part013
    + surrogateDiagTailX0RatChunk000Sub000Block087Part014
    + surrogateDiagTailX0RatChunk000Sub000Block087Part015
    + surrogateDiagTailX0RatChunk000Sub000Block087Part016
    + surrogateDiagTailX0RatChunk000Sub000Block087Part017
    + surrogateDiagTailX0RatChunk000Sub000Block087Part018
    + surrogateDiagTailX0RatChunk000Sub000Block087Part019
    + surrogateDiagTailX0RatChunk000Sub000Block087Part020
    + surrogateDiagTailX0RatChunk000Sub000Block087Part021
    + surrogateDiagTailX0RatChunk000Sub000Block087Part022
    + surrogateDiagTailX0RatChunk000Sub000Block087Part023
    + surrogateDiagTailX0RatChunk000Sub000Block087Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block087_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block087Head + surrogateDiagTailX0RatChunk000Sub000Block087Mid + surrogateDiagTailX0RatChunk000Sub000Block087Tail =
      surrogateDiagTailX0RatChunk000Sub000Block087 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block087Head surrogateDiagTailX0RatChunk000Sub000Block087Mid surrogateDiagTailX0RatChunk000Sub000Block087Tail surrogateDiagTailX0RatChunk000Sub000Block087
  ring

def SurrogateDiagonalTailChunk000Sub000Block087HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block087HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block087Head

def SurrogateDiagonalTailChunk000Sub000Block087MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block087MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block087Mid

def SurrogateDiagonalTailChunk000Sub000Block087TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block087TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block087Tail

theorem surrogateDiagonalTailChunk000Sub000Block087_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block087HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block087MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block087TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block087Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block087 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block087HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block087MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block087TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block087Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block087_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
