import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [191,192). -/

/-- Block 191 covers tail-support indices [4775,4800) and q from 7899 to 7941. -/

def TailChunk000Sub000Block191Part000SupportExplicit : Finset ℕ :=
  ([7899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part000 : ℚ :=
  (433189838075 : ℚ) / 959976022328623104

def SurrogateDiagonalTailChunk000Sub000Block191Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7899
    = surrogateDiagTailX0RatChunk000Sub000Block191Part000

theorem surrogateDiagonalTailChunk000Sub000Block191Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part000] using hcert

def TailChunk000Sub000Block191Part001SupportExplicit : Finset ℕ :=
  ([7901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7901
    = surrogateDiagTailX0RatChunk000Sub000Block191Part001

theorem surrogateDiagonalTailChunk000Sub000Block191Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part001] using hcert

def TailChunk000Sub000Block191Part002SupportExplicit : Finset ℕ :=
  ([7903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part002 : ℚ :=
  (399176121775 : ℚ) / 5246482867553599488

def SurrogateDiagonalTailChunk000Sub000Block191Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7903
    = surrogateDiagTailX0RatChunk000Sub000Block191Part002

theorem surrogateDiagonalTailChunk000Sub000Block191Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part002] using hcert

def TailChunk000Sub000Block191Part003SupportExplicit : Finset ℕ :=
  ([7905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part003 : ℚ :=
  (3264124813 : ℚ) / 2174762059038720

def SurrogateDiagonalTailChunk000Sub000Block191Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7905
    = surrogateDiagTailX0RatChunk000Sub000Block191Part003

theorem surrogateDiagonalTailChunk000Sub000Block191Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part003] using hcert

def TailChunk000Sub000Block191Part004SupportExplicit : Finset ℕ :=
  ([7906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part004 : ℚ :=
  (106015019375 : ℚ) / 59658463763851392

def SurrogateDiagonalTailChunk000Sub000Block191Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7906
    = surrogateDiagTailX0RatChunk000Sub000Block191Part004

theorem surrogateDiagonalTailChunk000Sub000Block191Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part004] using hcert

def TailChunk000Sub000Block191Part005SupportExplicit : Finset ℕ :=
  ([7907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7907
    = surrogateDiagTailX0RatChunk000Sub000Block191Part005

theorem surrogateDiagonalTailChunk000Sub000Block191Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part005] using hcert

def TailChunk000Sub000Block191Part006SupportExplicit : Finset ℕ :=
  ([7909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part006 : ℚ :=
  (3045303723 : ℚ) / 88606049191638400

def SurrogateDiagonalTailChunk000Sub000Block191Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7909
    = surrogateDiagTailX0RatChunk000Sub000Block191Part006

theorem surrogateDiagonalTailChunk000Sub000Block191Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part006] using hcert

def TailChunk000Sub000Block191Part007SupportExplicit : Finset ℕ :=
  ([7910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part007 : ℚ :=
  (724944956125 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block191Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7910
    = surrogateDiagTailX0RatChunk000Sub000Block191Part007

theorem surrogateDiagonalTailChunk000Sub000Block191Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part007] using hcert

def TailChunk000Sub000Block191Part008SupportExplicit : Finset ℕ :=
  ([7913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part008 : ℚ :=
  (480712763 : ℚ) / 57993654907699200

def SurrogateDiagonalTailChunk000Sub000Block191Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7913
    = surrogateDiagTailX0RatChunk000Sub000Block191Part008

theorem surrogateDiagonalTailChunk000Sub000Block191Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part008] using hcert

def TailChunk000Sub000Block191Part009SupportExplicit : Finset ℕ :=
  ([7914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part009 : ℚ :=
  (65204625 : ℚ) / 12070399165504

def SurrogateDiagonalTailChunk000Sub000Block191Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7914
    = surrogateDiagTailX0RatChunk000Sub000Block191Part009

theorem surrogateDiagonalTailChunk000Sub000Block191Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part009] using hcert

def TailChunk000Sub000Block191Part010SupportExplicit : Finset ℕ :=
  ([7915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part010 : ℚ :=
  (104425887525 : ℚ) / 668253882203737088

def SurrogateDiagonalTailChunk000Sub000Block191Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7915
    = surrogateDiagTailX0RatChunk000Sub000Block191Part010

theorem surrogateDiagonalTailChunk000Sub000Block191Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part010] using hcert

def TailChunk000Sub000Block191Part011SupportExplicit : Finset ℕ :=
  ([7917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part011 : ℚ :=
  (115486044025 : ℚ) / 94408459822301184

def SurrogateDiagonalTailChunk000Sub000Block191Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7917
    = surrogateDiagTailX0RatChunk000Sub000Block191Part011

theorem surrogateDiagonalTailChunk000Sub000Block191Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part011] using hcert

def TailChunk000Sub000Block191Part012SupportExplicit : Finset ℕ :=
  ([7918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part012 : ℚ :=
  (476875656875 : ℚ) / 265112574618461184

def SurrogateDiagonalTailChunk000Sub000Block191Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7918
    = surrogateDiagTailX0RatChunk000Sub000Block191Part012

theorem surrogateDiagonalTailChunk000Sub000Block191Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part012] using hcert

def TailChunk000Sub000Block191Part013SupportExplicit : Finset ℕ :=
  ([7919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7919
    = surrogateDiagTailX0RatChunk000Sub000Block191Part013

theorem surrogateDiagonalTailChunk000Sub000Block191Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part013] using hcert

def TailChunk000Sub000Block191Part014SupportExplicit : Finset ℕ :=
  ([7922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part014 : ℚ :=
  (936979358725 : ℚ) / 474743174036717568

def SurrogateDiagonalTailChunk000Sub000Block191Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7922
    = surrogateDiagTailX0RatChunk000Sub000Block191Part014

theorem surrogateDiagonalTailChunk000Sub000Block191Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part014] using hcert

def TailChunk000Sub000Block191Part015SupportExplicit : Finset ℕ :=
  ([7923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part015 : ℚ :=
  (8015189525 : ℚ) / 14103582784206336

def SurrogateDiagonalTailChunk000Sub000Block191Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7923
    = surrogateDiagTailX0RatChunk000Sub000Block191Part015

theorem surrogateDiagonalTailChunk000Sub000Block191Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part015] using hcert

def TailChunk000Sub000Block191Part016SupportExplicit : Finset ℕ :=
  ([7926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part016 : ℚ :=
  (30522218377 : ℚ) / 4858503922483200

def SurrogateDiagonalTailChunk000Sub000Block191Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7926
    = surrogateDiagTailX0RatChunk000Sub000Block191Part016

theorem surrogateDiagonalTailChunk000Sub000Block191Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part016] using hcert

def TailChunk000Sub000Block191Part017SupportExplicit : Finset ℕ :=
  ([7927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7927
    = surrogateDiagTailX0RatChunk000Sub000Block191Part017

theorem surrogateDiagonalTailChunk000Sub000Block191Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part017] using hcert

def TailChunk000Sub000Block191Part018SupportExplicit : Finset ℕ :=
  ([7930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part018 : ℚ :=
  (30523158511 : ℚ) / 6881083077427200

def SurrogateDiagonalTailChunk000Sub000Block191Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7930
    = surrogateDiagTailX0RatChunk000Sub000Block191Part018

theorem surrogateDiagonalTailChunk000Sub000Block191Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part018] using hcert

def TailChunk000Sub000Block191Part019SupportExplicit : Finset ℕ :=
  ([7931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part019 : ℚ :=
  (3110466407 : ℚ) / 23385210762931200

def SurrogateDiagonalTailChunk000Sub000Block191Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7931
    = surrogateDiagTailX0RatChunk000Sub000Block191Part019

theorem surrogateDiagonalTailChunk000Sub000Block191Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part019] using hcert

def TailChunk000Sub000Block191Part020SupportExplicit : Finset ℕ :=
  ([7933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block191Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7933
    = surrogateDiagTailX0RatChunk000Sub000Block191Part020

theorem surrogateDiagonalTailChunk000Sub000Block191Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part020] using hcert

def TailChunk000Sub000Block191Part021SupportExplicit : Finset ℕ :=
  ([7934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part021 : ℚ :=
  (245892015625 : ℚ) / 154659893588769042

def SurrogateDiagonalTailChunk000Sub000Block191Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7934
    = surrogateDiagTailX0RatChunk000Sub000Block191Part021

theorem surrogateDiagonalTailChunk000Sub000Block191Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part021] using hcert

def TailChunk000Sub000Block191Part022SupportExplicit : Finset ℕ :=
  ([7937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part022 : ℚ :=
  (984312015625 : ℚ) / 2479553619167281152

def SurrogateDiagonalTailChunk000Sub000Block191Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7937
    = surrogateDiagTailX0RatChunk000Sub000Block191Part022

theorem surrogateDiagonalTailChunk000Sub000Block191Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part022] using hcert

def TailChunk000Sub000Block191Part023SupportExplicit : Finset ℕ :=
  ([7939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part023 : ℚ :=
  (150659364675 : ℚ) / 321987650093514752

def SurrogateDiagonalTailChunk000Sub000Block191Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7939
    = surrogateDiagTailX0RatChunk000Sub000Block191Part023

theorem surrogateDiagonalTailChunk000Sub000Block191Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part023] using hcert

def TailChunk000Sub000Block191Part024SupportExplicit : Finset ℕ :=
  ([7941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block191Part024 : ℚ :=
  (547221546775 : ℚ) / 490282294170023712

def SurrogateDiagonalTailChunk000Sub000Block191Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7941
    = surrogateDiagTailX0RatChunk000Sub000Block191Part024

theorem surrogateDiagonalTailChunk000Sub000Block191Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block191Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block191Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block191Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block191Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block191Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block191HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block191Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block191Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part000
    + surrogateDiagTailX0RatChunk000Sub000Block191Part001
    + surrogateDiagTailX0RatChunk000Sub000Block191Part002
    + surrogateDiagTailX0RatChunk000Sub000Block191Part003
    + surrogateDiagTailX0RatChunk000Sub000Block191Part004
    + surrogateDiagTailX0RatChunk000Sub000Block191Part005
    + surrogateDiagTailX0RatChunk000Sub000Block191Part006
    + surrogateDiagTailX0RatChunk000Sub000Block191Part007
    + surrogateDiagTailX0RatChunk000Sub000Block191Part008
    + surrogateDiagTailX0RatChunk000Sub000Block191Part009

def surrogateDiagonalTailChunk000Sub000Block191MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block191Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block191Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part010
    + surrogateDiagTailX0RatChunk000Sub000Block191Part011
    + surrogateDiagTailX0RatChunk000Sub000Block191Part012
    + surrogateDiagTailX0RatChunk000Sub000Block191Part013
    + surrogateDiagTailX0RatChunk000Sub000Block191Part014
    + surrogateDiagTailX0RatChunk000Sub000Block191Part015
    + surrogateDiagTailX0RatChunk000Sub000Block191Part016
    + surrogateDiagTailX0RatChunk000Sub000Block191Part017
    + surrogateDiagTailX0RatChunk000Sub000Block191Part018
    + surrogateDiagTailX0RatChunk000Sub000Block191Part019

def surrogateDiagonalTailChunk000Sub000Block191TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block191Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block191Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block191Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part020
    + surrogateDiagTailX0RatChunk000Sub000Block191Part021
    + surrogateDiagTailX0RatChunk000Sub000Block191Part022
    + surrogateDiagTailX0RatChunk000Sub000Block191Part023
    + surrogateDiagTailX0RatChunk000Sub000Block191Part024

def surrogateDiagonalTailChunk000Sub000Block191Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block191HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block191MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block191TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block191 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block191Part000
    + surrogateDiagTailX0RatChunk000Sub000Block191Part001
    + surrogateDiagTailX0RatChunk000Sub000Block191Part002
    + surrogateDiagTailX0RatChunk000Sub000Block191Part003
    + surrogateDiagTailX0RatChunk000Sub000Block191Part004
    + surrogateDiagTailX0RatChunk000Sub000Block191Part005
    + surrogateDiagTailX0RatChunk000Sub000Block191Part006
    + surrogateDiagTailX0RatChunk000Sub000Block191Part007
    + surrogateDiagTailX0RatChunk000Sub000Block191Part008
    + surrogateDiagTailX0RatChunk000Sub000Block191Part009
    + surrogateDiagTailX0RatChunk000Sub000Block191Part010
    + surrogateDiagTailX0RatChunk000Sub000Block191Part011
    + surrogateDiagTailX0RatChunk000Sub000Block191Part012
    + surrogateDiagTailX0RatChunk000Sub000Block191Part013
    + surrogateDiagTailX0RatChunk000Sub000Block191Part014
    + surrogateDiagTailX0RatChunk000Sub000Block191Part015
    + surrogateDiagTailX0RatChunk000Sub000Block191Part016
    + surrogateDiagTailX0RatChunk000Sub000Block191Part017
    + surrogateDiagTailX0RatChunk000Sub000Block191Part018
    + surrogateDiagTailX0RatChunk000Sub000Block191Part019
    + surrogateDiagTailX0RatChunk000Sub000Block191Part020
    + surrogateDiagTailX0RatChunk000Sub000Block191Part021
    + surrogateDiagTailX0RatChunk000Sub000Block191Part022
    + surrogateDiagTailX0RatChunk000Sub000Block191Part023
    + surrogateDiagTailX0RatChunk000Sub000Block191Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block191_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block191Head + surrogateDiagTailX0RatChunk000Sub000Block191Mid + surrogateDiagTailX0RatChunk000Sub000Block191Tail =
      surrogateDiagTailX0RatChunk000Sub000Block191 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block191Head surrogateDiagTailX0RatChunk000Sub000Block191Mid surrogateDiagTailX0RatChunk000Sub000Block191Tail surrogateDiagTailX0RatChunk000Sub000Block191
  ring

def SurrogateDiagonalTailChunk000Sub000Block191HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block191HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block191Head

def SurrogateDiagonalTailChunk000Sub000Block191MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block191MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block191Mid

def SurrogateDiagonalTailChunk000Sub000Block191TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block191TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block191Tail

theorem surrogateDiagonalTailChunk000Sub000Block191_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block191HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block191MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block191TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block191Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block191 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block191HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block191MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block191TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block191Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block191_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
