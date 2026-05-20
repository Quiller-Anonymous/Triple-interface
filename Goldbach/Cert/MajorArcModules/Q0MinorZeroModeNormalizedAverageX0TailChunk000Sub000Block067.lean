import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [67,68). -/

/- Block 067 covers tail-support indices [1675,1700) and q from 2806 to 2846. -/

def TailChunk000Sub000Block067Part000SupportExplicit : Finset ℕ :=
  ([2806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part000 : ℚ :=
  (585508579 : ℚ) / 12652353964800

def SurrogateDiagonalTailChunk000Sub000Block067Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2806
    = surrogateDiagTailX0RatChunk000Sub000Block067Part000

theorem surrogateDiagonalTailChunk000Sub000Block067Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part000] using hcert

def TailChunk000Sub000Block067Part001SupportExplicit : Finset ℕ :=
  ([2807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part001 : ℚ :=
  (2141758363 : ℚ) / 368713728000000

def SurrogateDiagonalTailChunk000Sub000Block067Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2807
    = surrogateDiagTailX0RatChunk000Sub000Block067Part001

theorem surrogateDiagonalTailChunk000Sub000Block067Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part001] using hcert

def TailChunk000Sub000Block067Part002SupportExplicit : Finset ℕ :=
  ([2810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part002 : ℚ :=
  (5113585629 : ℚ) / 52461135462400

def SurrogateDiagonalTailChunk000Sub000Block067Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2810
    = surrogateDiagTailX0RatChunk000Sub000Block067Part002

theorem surrogateDiagonalTailChunk000Sub000Block067Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part002] using hcert

def TailChunk000Sub000Block067Part003SupportExplicit : Finset ℕ :=
  ([2811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part003 : ℚ :=
  (603050050975 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block067Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2811
    = surrogateDiagTailX0RatChunk000Sub000Block067Part003

theorem surrogateDiagonalTailChunk000Sub000Block067Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part003] using hcert

def TailChunk000Sub000Block067Part004SupportExplicit : Finset ℕ :=
  ([2813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part004 : ℚ :=
  (940780381525 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block067Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2813
    = surrogateDiagTailX0RatChunk000Sub000Block067Part004

theorem surrogateDiagonalTailChunk000Sub000Block067Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part004] using hcert

def TailChunk000Sub000Block067Part005SupportExplicit : Finset ℕ :=
  ([2814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part005 : ℚ :=
  (225624054325 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block067Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2814
    = surrogateDiagTailX0RatChunk000Sub000Block067Part005

theorem surrogateDiagonalTailChunk000Sub000Block067Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part005] using hcert

def TailChunk000Sub000Block067Part006SupportExplicit : Finset ℕ :=
  ([2815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part006 : ℚ :=
  (250504221525 : ℚ) / 21285841882126336

def SurrogateDiagonalTailChunk000Sub000Block067Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2815
    = surrogateDiagTailX0RatChunk000Sub000Block067Part006

theorem surrogateDiagonalTailChunk000Sub000Block067Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part006] using hcert

def TailChunk000Sub000Block067Part007SupportExplicit : Finset ℕ :=
  ([2818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part007 : ℚ :=
  (248011228925 : ℚ) / 4913686929997824

def SurrogateDiagonalTailChunk000Sub000Block067Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2818
    = surrogateDiagTailX0RatChunk000Sub000Block067Part007

theorem surrogateDiagonalTailChunk000Sub000Block067Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part007] using hcert

def TailChunk000Sub000Block067Part008SupportExplicit : Finset ℕ :=
  ([2819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part008 : ℚ :=
  (993146455975 : ℚ) / 157685156683631688

def SurrogateDiagonalTailChunk000Sub000Block067Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2819
    = surrogateDiagTailX0RatChunk000Sub000Block067Part008

theorem surrogateDiagonalTailChunk000Sub000Block067Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part008] using hcert

def TailChunk000Sub000Block067Part009SupportExplicit : Finset ℕ :=
  ([2821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part009 : ℚ :=
  (29753334493 : ℚ) / 2177217692467200

def SurrogateDiagonalTailChunk000Sub000Block067Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2821
    = surrogateDiagTailX0RatChunk000Sub000Block067Part009

theorem surrogateDiagonalTailChunk000Sub000Block067Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part009] using hcert

def TailChunk000Sub000Block067Part010SupportExplicit : Finset ℕ :=
  ([2822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part010 : ℚ :=
  (117238762125 : ℚ) / 2469681476141056

def SurrogateDiagonalTailChunk000Sub000Block067Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2822
    = surrogateDiagTailX0RatChunk000Sub000Block067Part010

theorem surrogateDiagonalTailChunk000Sub000Block067Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part010] using hcert

def TailChunk000Sub000Block067Part011SupportExplicit : Finset ℕ :=
  ([2823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part011 : ℚ :=
  (3539750687 : ℚ) / 249889635133440

def SurrogateDiagonalTailChunk000Sub000Block067Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2823
    = surrogateDiagTailX0RatChunk000Sub000Block067Part011

theorem surrogateDiagonalTailChunk000Sub000Block067Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part011] using hcert

def TailChunk000Sub000Block067Part012SupportExplicit : Finset ℕ :=
  ([2827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part012 : ℚ :=
  (17842346963 : ℚ) / 2147913144729600

def SurrogateDiagonalTailChunk000Sub000Block067Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2827
    = surrogateDiagTailX0RatChunk000Sub000Block067Part012

theorem surrogateDiagonalTailChunk000Sub000Block067Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part012] using hcert

def TailChunk000Sub000Block067Part013SupportExplicit : Finset ℕ :=
  ([2829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part013 : ℚ :=
  (22757966641 : ℚ) / 959704478515200

def SurrogateDiagonalTailChunk000Sub000Block067Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2829
    = surrogateDiagTailX0RatChunk000Sub000Block067Part013

theorem surrogateDiagonalTailChunk000Sub000Block067Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part013] using hcert

def TailChunk000Sub000Block067Part014SupportExplicit : Finset ℕ :=
  ([2830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part014 : ℚ :=
  (157213295975 : ℚ) / 2024106044580864

def SurrogateDiagonalTailChunk000Sub000Block067Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2830
    = surrogateDiagTailX0RatChunk000Sub000Block067Part014

theorem surrogateDiagonalTailChunk000Sub000Block067Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part014] using hcert

def TailChunk000Sub000Block067Part015SupportExplicit : Finset ℕ :=
  ([2831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part015 : ℚ :=
  (312227391625 : ℚ) / 41980005017819136

def SurrogateDiagonalTailChunk000Sub000Block067Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2831
    = surrogateDiagTailX0RatChunk000Sub000Block067Part015

theorem surrogateDiagonalTailChunk000Sub000Block067Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part015] using hcert

def TailChunk000Sub000Block067Part016SupportExplicit : Finset ℕ :=
  ([2833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part016 : ℚ :=
  (1003035477775 : ℚ) / 160842144521945088

def SurrogateDiagonalTailChunk000Sub000Block067Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2833
    = surrogateDiagTailX0RatChunk000Sub000Block067Part016

theorem surrogateDiagonalTailChunk000Sub000Block067Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part016] using hcert

def TailChunk000Sub000Block067Part017SupportExplicit : Finset ℕ :=
  ([2834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part017 : ℚ :=
  (454322441125 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub000Block067Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2834
    = surrogateDiagTailX0RatChunk000Sub000Block067Part017

theorem surrogateDiagonalTailChunk000Sub000Block067Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part017] using hcert

def TailChunk000Sub000Block067Part018SupportExplicit : Finset ℕ :=
  ([2837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part018 : ℚ :=
  (1005869910775 : ℚ) / 161752784255073408

def SurrogateDiagonalTailChunk000Sub000Block067Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2837
    = surrogateDiagTailX0RatChunk000Sub000Block067Part018

theorem surrogateDiagonalTailChunk000Sub000Block067Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part018] using hcert

def TailChunk000Sub000Block067Part019SupportExplicit : Finset ℕ :=
  ([2838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part019 : ℚ :=
  (478706867 : ℚ) / 2489854671360

def SurrogateDiagonalTailChunk000Sub000Block067Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2838
    = surrogateDiagTailX0RatChunk000Sub000Block067Part019

theorem surrogateDiagonalTailChunk000Sub000Block067Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part019] using hcert

def TailChunk000Sub000Block067Part020SupportExplicit : Finset ℕ :=
  ([2839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part020 : ℚ :=
  (164716069125 : ℚ) / 41478007610146816

def SurrogateDiagonalTailChunk000Sub000Block067Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2839
    = surrogateDiagTailX0RatChunk000Sub000Block067Part020

theorem surrogateDiagonalTailChunk000Sub000Block067Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part020] using hcert

def TailChunk000Sub000Block067Part021SupportExplicit : Finset ℕ :=
  ([2841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part021 : ℚ :=
  (134362275 : ℚ) / 6406997176448

def SurrogateDiagonalTailChunk000Sub000Block067Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2841
    = surrogateDiagTailX0RatChunk000Sub000Block067Part021

theorem surrogateDiagonalTailChunk000Sub000Block067Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part021] using hcert

def TailChunk000Sub000Block067Part022SupportExplicit : Finset ℕ :=
  ([2843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part022 : ℚ :=
  (1010129058775 : ℚ) / 163125987316968648

def SurrogateDiagonalTailChunk000Sub000Block067Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2843
    = surrogateDiagTailX0RatChunk000Sub000Block067Part022

theorem surrogateDiagonalTailChunk000Sub000Block067Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part022] using hcert

def TailChunk000Sub000Block067Part023SupportExplicit : Finset ℕ :=
  ([2845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part023 : ℚ :=
  (196949525275 : ℚ) / 16657130020012032

def SurrogateDiagonalTailChunk000Sub000Block067Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2845
    = surrogateDiagTailX0RatChunk000Sub000Block067Part023

theorem surrogateDiagonalTailChunk000Sub000Block067Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part023] using hcert

def TailChunk000Sub000Block067Part024SupportExplicit : Finset ℕ :=
  ([2846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block067Part024 : ℚ :=
  (42169146425 : ℚ) / 1136011518832392

def SurrogateDiagonalTailChunk000Sub000Block067Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2846
    = surrogateDiagTailX0RatChunk000Sub000Block067Part024

theorem surrogateDiagonalTailChunk000Sub000Block067Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block067Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block067Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block067Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block067Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block067Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block067HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block067Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block067Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block067Part000
    + surrogateDiagTailX0RatChunk000Sub000Block067Part001
    + surrogateDiagTailX0RatChunk000Sub000Block067Part002
    + surrogateDiagTailX0RatChunk000Sub000Block067Part003
    + surrogateDiagTailX0RatChunk000Sub000Block067Part004
    + surrogateDiagTailX0RatChunk000Sub000Block067Part005
    + surrogateDiagTailX0RatChunk000Sub000Block067Part006
    + surrogateDiagTailX0RatChunk000Sub000Block067Part007
    + surrogateDiagTailX0RatChunk000Sub000Block067Part008
    + surrogateDiagTailX0RatChunk000Sub000Block067Part009

def surrogateDiagonalTailChunk000Sub000Block067MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block067Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block067Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block067Part010
    + surrogateDiagTailX0RatChunk000Sub000Block067Part011
    + surrogateDiagTailX0RatChunk000Sub000Block067Part012
    + surrogateDiagTailX0RatChunk000Sub000Block067Part013
    + surrogateDiagTailX0RatChunk000Sub000Block067Part014
    + surrogateDiagTailX0RatChunk000Sub000Block067Part015
    + surrogateDiagTailX0RatChunk000Sub000Block067Part016
    + surrogateDiagTailX0RatChunk000Sub000Block067Part017
    + surrogateDiagTailX0RatChunk000Sub000Block067Part018
    + surrogateDiagTailX0RatChunk000Sub000Block067Part019

def surrogateDiagonalTailChunk000Sub000Block067TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block067Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block067Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block067Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block067Part020
    + surrogateDiagTailX0RatChunk000Sub000Block067Part021
    + surrogateDiagTailX0RatChunk000Sub000Block067Part022
    + surrogateDiagTailX0RatChunk000Sub000Block067Part023
    + surrogateDiagTailX0RatChunk000Sub000Block067Part024

def surrogateDiagonalTailChunk000Sub000Block067Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block067HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block067MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block067TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block067 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block067Part000
    + surrogateDiagTailX0RatChunk000Sub000Block067Part001
    + surrogateDiagTailX0RatChunk000Sub000Block067Part002
    + surrogateDiagTailX0RatChunk000Sub000Block067Part003
    + surrogateDiagTailX0RatChunk000Sub000Block067Part004
    + surrogateDiagTailX0RatChunk000Sub000Block067Part005
    + surrogateDiagTailX0RatChunk000Sub000Block067Part006
    + surrogateDiagTailX0RatChunk000Sub000Block067Part007
    + surrogateDiagTailX0RatChunk000Sub000Block067Part008
    + surrogateDiagTailX0RatChunk000Sub000Block067Part009
    + surrogateDiagTailX0RatChunk000Sub000Block067Part010
    + surrogateDiagTailX0RatChunk000Sub000Block067Part011
    + surrogateDiagTailX0RatChunk000Sub000Block067Part012
    + surrogateDiagTailX0RatChunk000Sub000Block067Part013
    + surrogateDiagTailX0RatChunk000Sub000Block067Part014
    + surrogateDiagTailX0RatChunk000Sub000Block067Part015
    + surrogateDiagTailX0RatChunk000Sub000Block067Part016
    + surrogateDiagTailX0RatChunk000Sub000Block067Part017
    + surrogateDiagTailX0RatChunk000Sub000Block067Part018
    + surrogateDiagTailX0RatChunk000Sub000Block067Part019
    + surrogateDiagTailX0RatChunk000Sub000Block067Part020
    + surrogateDiagTailX0RatChunk000Sub000Block067Part021
    + surrogateDiagTailX0RatChunk000Sub000Block067Part022
    + surrogateDiagTailX0RatChunk000Sub000Block067Part023
    + surrogateDiagTailX0RatChunk000Sub000Block067Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block067_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block067Head + surrogateDiagTailX0RatChunk000Sub000Block067Mid + surrogateDiagTailX0RatChunk000Sub000Block067Tail =
      surrogateDiagTailX0RatChunk000Sub000Block067 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block067Head surrogateDiagTailX0RatChunk000Sub000Block067Mid surrogateDiagTailX0RatChunk000Sub000Block067Tail surrogateDiagTailX0RatChunk000Sub000Block067
  ring

def SurrogateDiagonalTailChunk000Sub000Block067HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block067HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block067Head

def SurrogateDiagonalTailChunk000Sub000Block067MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block067MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block067Mid

def SurrogateDiagonalTailChunk000Sub000Block067TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block067TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block067Tail

theorem surrogateDiagonalTailChunk000Sub000Block067_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block067HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block067MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block067TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block067Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block067 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block067HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block067MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block067TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block067Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block067_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
