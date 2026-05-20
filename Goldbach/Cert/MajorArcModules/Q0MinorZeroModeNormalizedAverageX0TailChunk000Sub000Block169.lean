import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [169,170). -/

/-- Block 169 covers tail-support indices [4225,4250) and q from 7003 to 7043. -/

def TailChunk000Sub000Block169Part000SupportExplicit : Finset ℕ :=
  ([7003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part000 : ℚ :=
  (985571511675 : ℚ) / 1790539031274428416

def SurrogateDiagonalTailChunk000Sub000Block169Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7003
    = surrogateDiagTailX0RatChunk000Sub000Block169Part000

theorem surrogateDiagonalTailChunk000Sub000Block169Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part000] using hcert

def TailChunk000Sub000Block169Part001SupportExplicit : Finset ℕ :=
  ([7005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part001 : ℚ :=
  (222132821475 : ℚ) / 80496912523378688

def SurrogateDiagonalTailChunk000Sub000Block169Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7005
    = surrogateDiagTailX0RatChunk000Sub000Block169Part001

theorem surrogateDiagonalTailChunk000Sub000Block169Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part001] using hcert

def TailChunk000Sub000Block169Part002SupportExplicit : Finset ℕ :=
  ([7006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part002 : ℚ :=
  (14543997841 : ℚ) / 3187013979340800

def SurrogateDiagonalTailChunk000Sub000Block169Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7006
    = surrogateDiagTailX0RatChunk000Sub000Block169Part002

theorem surrogateDiagonalTailChunk000Sub000Block169Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part002] using hcert

def TailChunk000Sub000Block169Part003SupportExplicit : Finset ℕ :=
  ([7009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part003 : ℚ :=
  (46924534075 : ℚ) / 85063555054429056

def SurrogateDiagonalTailChunk000Sub000Block169Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7009
    = surrogateDiagTailX0RatChunk000Sub000Block169Part003

theorem surrogateDiagonalTailChunk000Sub000Block169Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part003] using hcert

def TailChunk000Sub000Block169Part004SupportExplicit : Finset ℕ :=
  ([7010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part004 : ℚ :=
  (45381819589 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk000Sub000Block169Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7010
    = surrogateDiagTailX0RatChunk000Sub000Block169Part004

theorem surrogateDiagonalTailChunk000Sub000Block169Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part004] using hcert

def TailChunk000Sub000Block169Part005SupportExplicit : Finset ℕ :=
  ([7013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part005 : ℚ :=
  (768471390625 : ℚ) / 1511243678551010592

def SurrogateDiagonalTailChunk000Sub000Block169Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7013
    = surrogateDiagTailX0RatChunk000Sub000Block169Part005

theorem surrogateDiagonalTailChunk000Sub000Block169Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part005] using hcert

def TailChunk000Sub000Block169Part006SupportExplicit : Finset ℕ :=
  ([7014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part006 : ℚ :=
  (261111511325 : ℚ) / 19685851268097024

def SurrogateDiagonalTailChunk000Sub000Block169Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7014
    = surrogateDiagTailX0RatChunk000Sub000Block169Part006

theorem surrogateDiagonalTailChunk000Sub000Block169Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part006] using hcert

def TailChunk000Sub000Block169Part007SupportExplicit : Finset ℕ :=
  ([7015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part007 : ℚ :=
  (2839729861 : ℚ) / 12956010459955200

def SurrogateDiagonalTailChunk000Sub000Block169Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7015
    = surrogateDiagTailX0RatChunk000Sub000Block169Part007

theorem surrogateDiagonalTailChunk000Sub000Block169Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part007] using hcert

def TailChunk000Sub000Block169Part008SupportExplicit : Finset ℕ :=
  ([7017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part008 : ℚ :=
  (341884367525 : ℚ) / 597715988644590144

def SurrogateDiagonalTailChunk000Sub000Block169Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7017
    = surrogateDiagTailX0RatChunk000Sub000Block169Part008

theorem surrogateDiagonalTailChunk000Sub000Block169Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part008] using hcert

def TailChunk000Sub000Block169Part009SupportExplicit : Finset ℕ :=
  ([7019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block169Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7019
    = surrogateDiagTailX0RatChunk000Sub000Block169Part009

theorem surrogateDiagonalTailChunk000Sub000Block169Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part009] using hcert

def TailChunk000Sub000Block169Part010SupportExplicit : Finset ℕ :=
  ([7021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part010 : ℚ :=
  (14959087625 : ℚ) / 89014345131884544

def SurrogateDiagonalTailChunk000Sub000Block169Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7021
    = surrogateDiagTailX0RatChunk000Sub000Block169Part010

theorem surrogateDiagonalTailChunk000Sub000Block169Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part010] using hcert

def TailChunk000Sub000Block169Part011SupportExplicit : Finset ℕ :=
  ([7022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part011 : ℚ :=
  (308178025 : ℚ) / 151815220982802

def SurrogateDiagonalTailChunk000Sub000Block169Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7022
    = surrogateDiagTailX0RatChunk000Sub000Block169Part011

theorem surrogateDiagonalTailChunk000Sub000Block169Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part011] using hcert

def TailChunk000Sub000Block169Part012SupportExplicit : Finset ℕ :=
  ([7023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part012 : ℚ :=
  (13698760019 : ℚ) / 23990553439257600

def SurrogateDiagonalTailChunk000Sub000Block169Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7023
    = surrogateDiagTailX0RatChunk000Sub000Block169Part012

theorem surrogateDiagonalTailChunk000Sub000Block169Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part012] using hcert

def TailChunk000Sub000Block169Part013SupportExplicit : Finset ℕ :=
  ([7026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part013 : ℚ :=
  (5481144623 : ℚ) / 599763835981440

def SurrogateDiagonalTailChunk000Sub000Block169Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7026
    = surrogateDiagTailX0RatChunk000Sub000Block169Part013

theorem surrogateDiagonalTailChunk000Sub000Block169Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part013] using hcert

def TailChunk000Sub000Block169Part014SupportExplicit : Finset ℕ :=
  ([7027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block169Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7027
    = surrogateDiagTailX0RatChunk000Sub000Block169Part014

theorem surrogateDiagonalTailChunk000Sub000Block169Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part014] using hcert

def TailChunk000Sub000Block169Part015SupportExplicit : Finset ℕ :=
  ([7030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part015 : ℚ :=
  (641260305625 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block169Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7030
    = surrogateDiagTailX0RatChunk000Sub000Block169Part015

theorem surrogateDiagonalTailChunk000Sub000Block169Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part015] using hcert

def TailChunk000Sub000Block169Part016SupportExplicit : Finset ℕ :=
  ([7031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part016 : ℚ :=
  (2863362625 : ℚ) / 308363845622317056

def SurrogateDiagonalTailChunk000Sub000Block169Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7031
    = surrogateDiagTailX0RatChunk000Sub000Block169Part016

theorem surrogateDiagonalTailChunk000Sub000Block169Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part016] using hcert

def TailChunk000Sub000Block169Part017SupportExplicit : Finset ℕ :=
  ([7033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part017 : ℚ :=
  (6700586659 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block169Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7033
    = surrogateDiagTailX0RatChunk000Sub000Block169Part017

theorem surrogateDiagonalTailChunk000Sub000Block169Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part017] using hcert

def TailChunk000Sub000Block169Part018SupportExplicit : Finset ℕ :=
  ([7034] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part018 : ℚ :=
  (193270140625 : ℚ) / 95534961552636192

def SurrogateDiagonalTailChunk000Sub000Block169Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7034
    = surrogateDiagTailX0RatChunk000Sub000Block169Part018

theorem surrogateDiagonalTailChunk000Sub000Block169Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part018] using hcert

def TailChunk000Sub000Block169Part019SupportExplicit : Finset ℕ :=
  ([7035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part019 : ℚ :=
  (215018890525 : ℚ) / 83954947780509696

def SurrogateDiagonalTailChunk000Sub000Block169Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7035
    = surrogateDiagTailX0RatChunk000Sub000Block169Part019

theorem surrogateDiagonalTailChunk000Sub000Block169Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part019] using hcert

def TailChunk000Sub000Block169Part020SupportExplicit : Finset ℕ :=
  ([7037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part020 : ℚ :=
  (3171691567 : ℚ) / 211351641731971200

def SurrogateDiagonalTailChunk000Sub000Block169Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7037
    = surrogateDiagTailX0RatChunk000Sub000Block169Part020

theorem surrogateDiagonalTailChunk000Sub000Block169Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part020] using hcert

def TailChunk000Sub000Block169Part021SupportExplicit : Finset ℕ :=
  ([7039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block169Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7039
    = surrogateDiagTailX0RatChunk000Sub000Block169Part021

theorem surrogateDiagonalTailChunk000Sub000Block169Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part021] using hcert

def TailChunk000Sub000Block169Part022SupportExplicit : Finset ℕ :=
  ([7041] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part022 : ℚ :=
  (344225898725 : ℚ) / 605938959732354624

def SurrogateDiagonalTailChunk000Sub000Block169Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7041
    = surrogateDiagTailX0RatChunk000Sub000Block169Part022

theorem surrogateDiagonalTailChunk000Sub000Block169Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part022] using hcert

def TailChunk000Sub000Block169Part023SupportExplicit : Finset ℕ :=
  ([7042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part023 : ℚ :=
  (695009088925 : ℚ) / 205800643790218368

def SurrogateDiagonalTailChunk000Sub000Block169Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7042
    = surrogateDiagTailX0RatChunk000Sub000Block169Part023

theorem surrogateDiagonalTailChunk000Sub000Block169Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part023] using hcert

def TailChunk000Sub000Block169Part024SupportExplicit : Finset ℕ :=
  ([7043] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block169Part024 : ℚ :=
  (775060140625 : ℚ) / 1537272826571506962

def SurrogateDiagonalTailChunk000Sub000Block169Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7043
    = surrogateDiagTailX0RatChunk000Sub000Block169Part024

theorem surrogateDiagonalTailChunk000Sub000Block169Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block169Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block169Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block169Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block169Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block169Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block169HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block169Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block169Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part000
    + surrogateDiagTailX0RatChunk000Sub000Block169Part001
    + surrogateDiagTailX0RatChunk000Sub000Block169Part002
    + surrogateDiagTailX0RatChunk000Sub000Block169Part003
    + surrogateDiagTailX0RatChunk000Sub000Block169Part004
    + surrogateDiagTailX0RatChunk000Sub000Block169Part005
    + surrogateDiagTailX0RatChunk000Sub000Block169Part006
    + surrogateDiagTailX0RatChunk000Sub000Block169Part007
    + surrogateDiagTailX0RatChunk000Sub000Block169Part008
    + surrogateDiagTailX0RatChunk000Sub000Block169Part009

def surrogateDiagonalTailChunk000Sub000Block169MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block169Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block169Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part010
    + surrogateDiagTailX0RatChunk000Sub000Block169Part011
    + surrogateDiagTailX0RatChunk000Sub000Block169Part012
    + surrogateDiagTailX0RatChunk000Sub000Block169Part013
    + surrogateDiagTailX0RatChunk000Sub000Block169Part014
    + surrogateDiagTailX0RatChunk000Sub000Block169Part015
    + surrogateDiagTailX0RatChunk000Sub000Block169Part016
    + surrogateDiagTailX0RatChunk000Sub000Block169Part017
    + surrogateDiagTailX0RatChunk000Sub000Block169Part018
    + surrogateDiagTailX0RatChunk000Sub000Block169Part019

def surrogateDiagonalTailChunk000Sub000Block169TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block169Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block169Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block169Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part020
    + surrogateDiagTailX0RatChunk000Sub000Block169Part021
    + surrogateDiagTailX0RatChunk000Sub000Block169Part022
    + surrogateDiagTailX0RatChunk000Sub000Block169Part023
    + surrogateDiagTailX0RatChunk000Sub000Block169Part024

def surrogateDiagonalTailChunk000Sub000Block169Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block169HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block169MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block169TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block169 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block169Part000
    + surrogateDiagTailX0RatChunk000Sub000Block169Part001
    + surrogateDiagTailX0RatChunk000Sub000Block169Part002
    + surrogateDiagTailX0RatChunk000Sub000Block169Part003
    + surrogateDiagTailX0RatChunk000Sub000Block169Part004
    + surrogateDiagTailX0RatChunk000Sub000Block169Part005
    + surrogateDiagTailX0RatChunk000Sub000Block169Part006
    + surrogateDiagTailX0RatChunk000Sub000Block169Part007
    + surrogateDiagTailX0RatChunk000Sub000Block169Part008
    + surrogateDiagTailX0RatChunk000Sub000Block169Part009
    + surrogateDiagTailX0RatChunk000Sub000Block169Part010
    + surrogateDiagTailX0RatChunk000Sub000Block169Part011
    + surrogateDiagTailX0RatChunk000Sub000Block169Part012
    + surrogateDiagTailX0RatChunk000Sub000Block169Part013
    + surrogateDiagTailX0RatChunk000Sub000Block169Part014
    + surrogateDiagTailX0RatChunk000Sub000Block169Part015
    + surrogateDiagTailX0RatChunk000Sub000Block169Part016
    + surrogateDiagTailX0RatChunk000Sub000Block169Part017
    + surrogateDiagTailX0RatChunk000Sub000Block169Part018
    + surrogateDiagTailX0RatChunk000Sub000Block169Part019
    + surrogateDiagTailX0RatChunk000Sub000Block169Part020
    + surrogateDiagTailX0RatChunk000Sub000Block169Part021
    + surrogateDiagTailX0RatChunk000Sub000Block169Part022
    + surrogateDiagTailX0RatChunk000Sub000Block169Part023
    + surrogateDiagTailX0RatChunk000Sub000Block169Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block169_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block169Head + surrogateDiagTailX0RatChunk000Sub000Block169Mid + surrogateDiagTailX0RatChunk000Sub000Block169Tail =
      surrogateDiagTailX0RatChunk000Sub000Block169 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block169Head surrogateDiagTailX0RatChunk000Sub000Block169Mid surrogateDiagTailX0RatChunk000Sub000Block169Tail surrogateDiagTailX0RatChunk000Sub000Block169
  ring

def SurrogateDiagonalTailChunk000Sub000Block169HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block169HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block169Head

def SurrogateDiagonalTailChunk000Sub000Block169MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block169MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block169Mid

def SurrogateDiagonalTailChunk000Sub000Block169TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block169TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block169Tail

theorem surrogateDiagonalTailChunk000Sub000Block169_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block169HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block169MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block169TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block169Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block169 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block169HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block169MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block169TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block169Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block169_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
