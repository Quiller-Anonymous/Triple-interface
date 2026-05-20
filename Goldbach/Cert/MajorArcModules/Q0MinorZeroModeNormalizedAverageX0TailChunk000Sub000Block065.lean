import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [65,66). -/

/- Block 065 covers tail-support indices [1625,1650) and q from 2722 to 2762. -/

def TailChunk000Sub000Block065Part000SupportExplicit : Finset ℕ :=
  ([2722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part000 : ℚ :=
  (9256048037 : ℚ) / 171085218201600

def SurrogateDiagonalTailChunk000Sub000Block065Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2722
    = surrogateDiagTailX0RatChunk000Sub000Block065Part000

theorem surrogateDiagonalTailChunk000Sub000Block065Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part000] using hcert

def TailChunk000Sub000Block065Part001SupportExplicit : Finset ℕ :=
  ([2723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part001 : ℚ :=
  (391485446225 : ℚ) / 36722206389003264

def SurrogateDiagonalTailChunk000Sub000Block065Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2723
    = surrogateDiagTailX0RatChunk000Sub000Block065Part001

theorem surrogateDiagonalTailChunk000Sub000Block065Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part001] using hcert

def TailChunk000Sub000Block065Part002SupportExplicit : Finset ℕ :=
  ([2726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part002 : ℚ :=
  (145612457325 : ℚ) / 2293871345145856

def SurrogateDiagonalTailChunk000Sub000Block065Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2726
    = surrogateDiagTailX0RatChunk000Sub000Block065Part002

theorem surrogateDiagonalTailChunk000Sub000Block065Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part002] using hcert

def TailChunk000Sub000Block065Part003SupportExplicit : Finset ℕ :=
  ([2729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part003 : ℚ :=
  (930743938975 : ℚ) / 138485506203568128

def SurrogateDiagonalTailChunk000Sub000Block065Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2729
    = surrogateDiagTailX0RatChunk000Sub000Block065Part003

theorem surrogateDiagonalTailChunk000Sub000Block065Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part003] using hcert

def TailChunk000Sub000Block065Part004SupportExplicit : Finset ℕ :=
  ([2730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part004 : ℚ :=
  (9458826875 : ℚ) / 15291295727616

def SurrogateDiagonalTailChunk000Sub000Block065Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2730
    = surrogateDiagTailX0RatChunk000Sub000Block065Part004

theorem surrogateDiagonalTailChunk000Sub000Block065Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part004] using hcert

def TailChunk000Sub000Block065Part005SupportExplicit : Finset ℕ :=
  ([2731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part005 : ℚ :=
  (186459025 : ℚ) / 55556827553682

def SurrogateDiagonalTailChunk000Sub000Block065Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2731
    = surrogateDiagTailX0RatChunk000Sub000Block065Part005

theorem surrogateDiagonalTailChunk000Sub000Block065Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part005] using hcert

def TailChunk000Sub000Block065Part006SupportExplicit : Finset ℕ :=
  ([2733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part006 : ℚ :=
  (994719 : ℚ) / 43887975040

def SurrogateDiagonalTailChunk000Sub000Block065Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2733
    = surrogateDiagTailX0RatChunk000Sub000Block065Part006

theorem surrogateDiagonalTailChunk000Sub000Block065Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part006] using hcert

def TailChunk000Sub000Block065Part007SupportExplicit : Finset ℕ :=
  ([2734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part007 : ℚ :=
  (233445973325 : ℚ) / 4353110190368484

def SurrogateDiagonalTailChunk000Sub000Block065Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2734
    = surrogateDiagTailX0RatChunk000Sub000Block065Part007

theorem surrogateDiagonalTailChunk000Sub000Block065Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part007] using hcert

def TailChunk000Sub000Block065Part008SupportExplicit : Finset ℕ :=
  ([2735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part008 : ℚ :=
  (13482374225 : ℚ) / 1053522063240192

def SurrogateDiagonalTailChunk000Sub000Block065Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2735
    = surrogateDiagTailX0RatChunk000Sub000Block065Part008

theorem surrogateDiagonalTailChunk000Sub000Block065Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part008] using hcert

def TailChunk000Sub000Block065Part009SupportExplicit : Finset ℕ :=
  ([2737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part009 : ℚ :=
  (354175255175 : ℚ) / 24875540083113984

def SurrogateDiagonalTailChunk000Sub000Block065Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2737
    = surrogateDiagTailX0RatChunk000Sub000Block065Part009

theorem surrogateDiagonalTailChunk000Sub000Block065Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part009] using hcert

def TailChunk000Sub000Block065Part010SupportExplicit : Finset ℕ :=
  ([2739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part010 : ℚ :=
  (22239134377 : ℚ) / 723539494963200

def SurrogateDiagonalTailChunk000Sub000Block065Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2739
    = surrogateDiagTailX0RatChunk000Sub000Block065Part010

theorem surrogateDiagonalTailChunk000Sub000Block065Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part010] using hcert

def TailChunk000Sub000Block065Part011SupportExplicit : Finset ℕ :=
  ([2741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part011 : ℚ :=
  (37557891919 : ℚ) / 5637533057155200

def SurrogateDiagonalTailChunk000Sub000Block065Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2741
    = surrogateDiagTailX0RatChunk000Sub000Block065Part011

theorem surrogateDiagonalTailChunk000Sub000Block065Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part011] using hcert

def TailChunk000Sub000Block065Part012SupportExplicit : Finset ℕ :=
  ([2742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part012 : ℚ :=
  (299588983225 : ℚ) / 1729841102880768

def SurrogateDiagonalTailChunk000Sub000Block065Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2742
    = surrogateDiagTailX0RatChunk000Sub000Block065Part012

theorem surrogateDiagonalTailChunk000Sub000Block065Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part012] using hcert

def TailChunk000Sub000Block065Part013SupportExplicit : Finset ℕ :=
  ([2743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part013 : ℚ :=
  (34333643011 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block065Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2743
    = surrogateDiagTailX0RatChunk000Sub000Block065Part013

theorem surrogateDiagonalTailChunk000Sub000Block065Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part013] using hcert

def TailChunk000Sub000Block065Part014SupportExplicit : Finset ℕ :=
  ([2746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part014 : ℚ :=
  (2403539475 : ℚ) / 60273438730624

def SurrogateDiagonalTailChunk000Sub000Block065Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2746
    = surrogateDiagTailX0RatChunk000Sub000Block065Part014

theorem surrogateDiagonalTailChunk000Sub000Block065Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part014] using hcert

def TailChunk000Sub000Block065Part015SupportExplicit : Finset ℕ :=
  ([2747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part015 : ℚ :=
  (9363510377 : ℚ) / 2429251961241600

def SurrogateDiagonalTailChunk000Sub000Block065Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2747
    = surrogateDiagTailX0RatChunk000Sub000Block065Part015

theorem surrogateDiagonalTailChunk000Sub000Block065Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part015] using hcert

def TailChunk000Sub000Block065Part016SupportExplicit : Finset ℕ :=
  ([2749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part016 : ℚ :=
  (944436199975 : ℚ) / 142591544261371008

def SurrogateDiagonalTailChunk000Sub000Block065Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2749
    = surrogateDiagTailX0RatChunk000Sub000Block065Part016

theorem surrogateDiagonalTailChunk000Sub000Block065Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part016] using hcert

def TailChunk000Sub000Block065Part017SupportExplicit : Finset ℕ :=
  ([2751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part017 : ℚ :=
  (167049323 : ℚ) / 5062900377600

def SurrogateDiagonalTailChunk000Sub000Block065Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2751
    = surrogateDiagTailX0RatChunk000Sub000Block065Part017

theorem surrogateDiagonalTailChunk000Sub000Block065Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part017] using hcert

def TailChunk000Sub000Block065Part018SupportExplicit : Finset ℕ :=
  ([2753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part018 : ℚ :=
  (947186649775 : ℚ) / 143423586076459008

def SurrogateDiagonalTailChunk000Sub000Block065Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2753
    = surrogateDiagTailX0RatChunk000Sub000Block065Part018

theorem surrogateDiagonalTailChunk000Sub000Block065Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part018] using hcert

def TailChunk000Sub000Block065Part019SupportExplicit : Finset ℕ :=
  ([2755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part019 : ℚ :=
  (672276443275 : ℚ) / 41303701172256768

def SurrogateDiagonalTailChunk000Sub000Block065Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2755
    = surrogateDiagTailX0RatChunk000Sub000Block065Part019

theorem surrogateDiagonalTailChunk000Sub000Block065Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part019] using hcert

def TailChunk000Sub000Block065Part020SupportExplicit : Finset ℕ :=
  ([2757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part020 : ℚ :=
  (580102629925 : ℚ) / 28413031076961408

def SurrogateDiagonalTailChunk000Sub000Block065Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2757
    = surrogateDiagTailX0RatChunk000Sub000Block065Part020

theorem surrogateDiagonalTailChunk000Sub000Block065Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part020] using hcert

def TailChunk000Sub000Block065Part021SupportExplicit : Finset ℕ :=
  ([2758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part021 : ℚ :=
  (44233813375 : ℚ) / 531390316972032

def SurrogateDiagonalTailChunk000Sub000Block065Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2758
    = surrogateDiagTailX0RatChunk000Sub000Block065Part021

theorem surrogateDiagonalTailChunk000Sub000Block065Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part021] using hcert

def TailChunk000Sub000Block065Part022SupportExplicit : Finset ℕ :=
  ([2759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part022 : ℚ :=
  (3628966549 : ℚ) / 485850392248320

def SurrogateDiagonalTailChunk000Sub000Block065Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2759
    = surrogateDiagTailX0RatChunk000Sub000Block065Part022

theorem surrogateDiagonalTailChunk000Sub000Block065Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part022] using hcert

def TailChunk000Sub000Block065Part023SupportExplicit : Finset ℕ :=
  ([2761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part023 : ℚ :=
  (2320501049 : ℚ) / 488378906250000

def SurrogateDiagonalTailChunk000Sub000Block065Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2761
    = surrogateDiagTailX0RatChunk000Sub000Block065Part023

theorem surrogateDiagonalTailChunk000Sub000Block065Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part023] using hcert

def TailChunk000Sub000Block065Part024SupportExplicit : Finset ℕ :=
  ([2762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block065Part024 : ℚ :=
  (1588665113 : ℚ) / 40305163420800

def SurrogateDiagonalTailChunk000Sub000Block065Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2762
    = surrogateDiagTailX0RatChunk000Sub000Block065Part024

theorem surrogateDiagonalTailChunk000Sub000Block065Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block065Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block065Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block065Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block065Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block065Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block065HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block065Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block065Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block065Part000
    + surrogateDiagTailX0RatChunk000Sub000Block065Part001
    + surrogateDiagTailX0RatChunk000Sub000Block065Part002
    + surrogateDiagTailX0RatChunk000Sub000Block065Part003
    + surrogateDiagTailX0RatChunk000Sub000Block065Part004
    + surrogateDiagTailX0RatChunk000Sub000Block065Part005
    + surrogateDiagTailX0RatChunk000Sub000Block065Part006
    + surrogateDiagTailX0RatChunk000Sub000Block065Part007
    + surrogateDiagTailX0RatChunk000Sub000Block065Part008
    + surrogateDiagTailX0RatChunk000Sub000Block065Part009

def surrogateDiagonalTailChunk000Sub000Block065MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block065Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block065Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block065Part010
    + surrogateDiagTailX0RatChunk000Sub000Block065Part011
    + surrogateDiagTailX0RatChunk000Sub000Block065Part012
    + surrogateDiagTailX0RatChunk000Sub000Block065Part013
    + surrogateDiagTailX0RatChunk000Sub000Block065Part014
    + surrogateDiagTailX0RatChunk000Sub000Block065Part015
    + surrogateDiagTailX0RatChunk000Sub000Block065Part016
    + surrogateDiagTailX0RatChunk000Sub000Block065Part017
    + surrogateDiagTailX0RatChunk000Sub000Block065Part018
    + surrogateDiagTailX0RatChunk000Sub000Block065Part019

def surrogateDiagonalTailChunk000Sub000Block065TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block065Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block065Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block065Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block065Part020
    + surrogateDiagTailX0RatChunk000Sub000Block065Part021
    + surrogateDiagTailX0RatChunk000Sub000Block065Part022
    + surrogateDiagTailX0RatChunk000Sub000Block065Part023
    + surrogateDiagTailX0RatChunk000Sub000Block065Part024

def surrogateDiagonalTailChunk000Sub000Block065Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block065HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block065MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block065TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block065 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block065Part000
    + surrogateDiagTailX0RatChunk000Sub000Block065Part001
    + surrogateDiagTailX0RatChunk000Sub000Block065Part002
    + surrogateDiagTailX0RatChunk000Sub000Block065Part003
    + surrogateDiagTailX0RatChunk000Sub000Block065Part004
    + surrogateDiagTailX0RatChunk000Sub000Block065Part005
    + surrogateDiagTailX0RatChunk000Sub000Block065Part006
    + surrogateDiagTailX0RatChunk000Sub000Block065Part007
    + surrogateDiagTailX0RatChunk000Sub000Block065Part008
    + surrogateDiagTailX0RatChunk000Sub000Block065Part009
    + surrogateDiagTailX0RatChunk000Sub000Block065Part010
    + surrogateDiagTailX0RatChunk000Sub000Block065Part011
    + surrogateDiagTailX0RatChunk000Sub000Block065Part012
    + surrogateDiagTailX0RatChunk000Sub000Block065Part013
    + surrogateDiagTailX0RatChunk000Sub000Block065Part014
    + surrogateDiagTailX0RatChunk000Sub000Block065Part015
    + surrogateDiagTailX0RatChunk000Sub000Block065Part016
    + surrogateDiagTailX0RatChunk000Sub000Block065Part017
    + surrogateDiagTailX0RatChunk000Sub000Block065Part018
    + surrogateDiagTailX0RatChunk000Sub000Block065Part019
    + surrogateDiagTailX0RatChunk000Sub000Block065Part020
    + surrogateDiagTailX0RatChunk000Sub000Block065Part021
    + surrogateDiagTailX0RatChunk000Sub000Block065Part022
    + surrogateDiagTailX0RatChunk000Sub000Block065Part023
    + surrogateDiagTailX0RatChunk000Sub000Block065Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block065_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block065Head + surrogateDiagTailX0RatChunk000Sub000Block065Mid + surrogateDiagTailX0RatChunk000Sub000Block065Tail =
      surrogateDiagTailX0RatChunk000Sub000Block065 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block065Head surrogateDiagTailX0RatChunk000Sub000Block065Mid surrogateDiagTailX0RatChunk000Sub000Block065Tail surrogateDiagTailX0RatChunk000Sub000Block065
  ring

def SurrogateDiagonalTailChunk000Sub000Block065HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block065HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block065Head

def SurrogateDiagonalTailChunk000Sub000Block065MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block065MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block065Mid

def SurrogateDiagonalTailChunk000Sub000Block065TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block065TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block065Tail

theorem surrogateDiagonalTailChunk000Sub000Block065_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block065HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block065MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block065TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block065Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block065 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block065HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block065MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block065TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block065Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block065_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
