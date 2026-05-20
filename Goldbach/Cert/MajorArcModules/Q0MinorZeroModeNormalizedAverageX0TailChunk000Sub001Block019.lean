import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [19,20). -/

/-- Block 019 covers tail-support indices [5475,5500) and q from 9053 to 9093. -/

def TailChunk000Sub001Block019Part000SupportExplicit : Finset ℕ :=
  ([9053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part000 : ℚ :=
  (1025020039 : ℚ) / 45664017762957120

def SurrogateDiagonalTailChunk000Sub001Block019Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9053
    = surrogateDiagTailX0RatChunk000Sub001Block019Part000

theorem surrogateDiagonalTailChunk000Sub001Block019Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part000] using hcert

def TailChunk000Sub001Block019Part001SupportExplicit : Finset ℕ :=
  ([9055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part001 : ℚ :=
  (16427247169 : ℚ) / 274815431071795200

def SurrogateDiagonalTailChunk000Sub001Block019Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9055
    = surrogateDiagTailX0RatChunk000Sub001Block019Part001

theorem surrogateDiagonalTailChunk000Sub001Block019Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part001] using hcert

def TailChunk000Sub001Block019Part002SupportExplicit : Finset ℕ :=
  ([9057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part002 : ℚ :=
  (569468807525 : ℚ) / 1659563168043875904

def SurrogateDiagonalTailChunk000Sub001Block019Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9057
    = surrogateDiagTailX0RatChunk000Sub001Block019Part002

theorem surrogateDiagonalTailChunk000Sub001Block019Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part002] using hcert

def TailChunk000Sub001Block019Part003SupportExplicit : Finset ℕ :=
  ([9058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part003 : ℚ :=
  (280906999375 : ℚ) / 141091854251664672

def SurrogateDiagonalTailChunk000Sub001Block019Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9058
    = surrogateDiagTailX0RatChunk000Sub001Block019Part003

theorem surrogateDiagonalTailChunk000Sub001Block019Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part003] using hcert

def TailChunk000Sub001Block019Part004SupportExplicit : Finset ℕ :=
  ([9059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block019Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9059
    = surrogateDiagTailX0RatChunk000Sub001Block019Part004

theorem surrogateDiagonalTailChunk000Sub001Block019Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part004] using hcert

def TailChunk000Sub001Block019Part005SupportExplicit : Finset ℕ :=
  ([9061] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part005 : ℚ :=
  (5064684317 : ℚ) / 115987309815398400

def SurrogateDiagonalTailChunk000Sub001Block019Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9061
    = surrogateDiagTailX0RatChunk000Sub001Block019Part005

theorem surrogateDiagonalTailChunk000Sub001Block019Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part005] using hcert

def TailChunk000Sub001Block019Part006SupportExplicit : Finset ℕ :=
  ([9062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part006 : ℚ :=
  (102231913725 : ℚ) / 72037829914699264

def SurrogateDiagonalTailChunk000Sub001Block019Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9062
    = surrogateDiagTailX0RatChunk000Sub001Block019Part006

theorem surrogateDiagonalTailChunk000Sub001Block019Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part006] using hcert

def TailChunk000Sub001Block019Part007SupportExplicit : Finset ℕ :=
  ([9066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part007 : ℚ :=
  (39933581287 : ℚ) / 8319833249923200

def SurrogateDiagonalTailChunk000Sub001Block019Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9066
    = surrogateDiagTailX0RatChunk000Sub001Block019Part007

theorem surrogateDiagonalTailChunk000Sub001Block019Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part007] using hcert

def TailChunk000Sub001Block019Part008SupportExplicit : Finset ℕ :=
  ([9067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block019Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9067
    = surrogateDiagTailX0RatChunk000Sub001Block019Part008

theorem surrogateDiagonalTailChunk000Sub001Block019Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part008] using hcert

def TailChunk000Sub001Block019Part009SupportExplicit : Finset ℕ :=
  ([9069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part009 : ℚ :=
  (570978505325 : ℚ) / 1668378889261161024

def SurrogateDiagonalTailChunk000Sub001Block019Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9069
    = surrogateDiagTailX0RatChunk000Sub001Block019Part009

theorem surrogateDiagonalTailChunk000Sub001Block019Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part009] using hcert

def TailChunk000Sub001Block019Part010SupportExplicit : Finset ℕ :=
  ([9070] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part010 : ℚ :=
  (513750104375 : ℚ) / 215650077838009344

def SurrogateDiagonalTailChunk000Sub001Block019Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9070
    = surrogateDiagTailX0RatChunk000Sub001Block019Part010

theorem surrogateDiagonalTailChunk000Sub001Block019Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part010] using hcert

def TailChunk000Sub001Block019Part011SupportExplicit : Finset ℕ :=
  ([9071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part011 : ℚ :=
  (36964641425 : ℚ) / 7607344867043180544

def SurrogateDiagonalTailChunk000Sub001Block019Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9071
    = surrogateDiagTailX0RatChunk000Sub001Block019Part011

theorem surrogateDiagonalTailChunk000Sub001Block019Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part011] using hcert

def TailChunk000Sub001Block019Part012SupportExplicit : Finset ℕ :=
  ([9073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part012 : ℚ :=
  (6505721 : ℚ) / 1245446055403200

def SurrogateDiagonalTailChunk000Sub001Block019Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9073
    = surrogateDiagTailX0RatChunk000Sub001Block019Part012

theorem surrogateDiagonalTailChunk000Sub001Block019Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part012] using hcert

def TailChunk000Sub001Block019Part013SupportExplicit : Finset ℕ :=
  ([9074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part013 : ℚ :=
  (1192313545225 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk000Sub001Block019Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9074
    = surrogateDiagTailX0RatChunk000Sub001Block019Part013

theorem surrogateDiagonalTailChunk000Sub001Block019Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part013] using hcert

def TailChunk000Sub001Block019Part014SupportExplicit : Finset ℕ :=
  ([9077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part014 : ℚ :=
  (17630358625 : ℚ) / 2427314833705402368

def SurrogateDiagonalTailChunk000Sub001Block019Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9077
    = surrogateDiagTailX0RatChunk000Sub001Block019Part014

theorem surrogateDiagonalTailChunk000Sub001Block019Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part014] using hcert

def TailChunk000Sub001Block019Part015SupportExplicit : Finset ℕ :=
  ([9078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part015 : ℚ :=
  (161117925 : ℚ) / 31441308090368

def SurrogateDiagonalTailChunk000Sub001Block019Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9078
    = surrogateDiagTailX0RatChunk000Sub001Block019Part015

theorem surrogateDiagonalTailChunk000Sub001Block019Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part015] using hcert

def TailChunk000Sub001Block019Part016SupportExplicit : Finset ℕ :=
  ([9079] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part016 : ℚ :=
  (421526490325 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block019Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9079
    = surrogateDiagTailX0RatChunk000Sub001Block019Part016

theorem surrogateDiagonalTailChunk000Sub001Block019Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part016] using hcert

def TailChunk000Sub001Block019Part017SupportExplicit : Finset ℕ :=
  ([9082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part017 : ℚ :=
  (1220149478425 : ℚ) / 842218365626967168

def SurrogateDiagonalTailChunk000Sub001Block019Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9082
    = surrogateDiagTailX0RatChunk000Sub001Block019Part017

theorem surrogateDiagonalTailChunk000Sub001Block019Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part017] using hcert

def TailChunk000Sub001Block019Part018SupportExplicit : Finset ℕ :=
  ([9083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part018 : ℚ :=
  (265764779 : ℚ) / 39265579904071680

def SurrogateDiagonalTailChunk000Sub001Block019Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9083
    = surrogateDiagTailX0RatChunk000Sub001Block019Part018

theorem surrogateDiagonalTailChunk000Sub001Block019Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part018] using hcert

def TailChunk000Sub001Block019Part019SupportExplicit : Finset ℕ :=
  ([9085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part019 : ℚ :=
  (492987596875 : ℚ) / 5550549221201707008

def SurrogateDiagonalTailChunk000Sub001Block019Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9085
    = surrogateDiagTailX0RatChunk000Sub001Block019Part019

theorem surrogateDiagonalTailChunk000Sub001Block019Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part019] using hcert

def TailChunk000Sub001Block019Part020SupportExplicit : Finset ℕ :=
  ([9086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part020 : ℚ :=
  (40795149109 : ℚ) / 14669112051763200

def SurrogateDiagonalTailChunk000Sub001Block019Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9086
    = surrogateDiagTailX0RatChunk000Sub001Block019Part020

theorem surrogateDiagonalTailChunk000Sub001Block019Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part020] using hcert

def TailChunk000Sub001Block019Part021SupportExplicit : Finset ℕ :=
  ([9087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part021 : ℚ :=
  (633220261975 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub001Block019Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9087
    = surrogateDiagTailX0RatChunk000Sub001Block019Part021

theorem surrogateDiagonalTailChunk000Sub001Block019Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part021] using hcert

def TailChunk000Sub001Block019Part022SupportExplicit : Finset ℕ :=
  ([9089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part022 : ℚ :=
  (433289611 : ℚ) / 103654333377331200

def SurrogateDiagonalTailChunk000Sub001Block019Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9089
    = surrogateDiagTailX0RatChunk000Sub001Block019Part022

theorem surrogateDiagonalTailChunk000Sub001Block019Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part022] using hcert

def TailChunk000Sub001Block019Part023SupportExplicit : Finset ℕ :=
  ([9091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part023 : ℚ :=
  (2066157025 : ℚ) / 6828768390191922

def SurrogateDiagonalTailChunk000Sub001Block019Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9091
    = surrogateDiagTailX0RatChunk000Sub001Block019Part023

theorem surrogateDiagonalTailChunk000Sub001Block019Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part023] using hcert

def TailChunk000Sub001Block019Part024SupportExplicit : Finset ℕ :=
  ([9093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block019Part024 : ℚ :=
  (2325222574975 : ℚ) / 1805871442839994368

def SurrogateDiagonalTailChunk000Sub001Block019Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9093
    = surrogateDiagTailX0RatChunk000Sub001Block019Part024

theorem surrogateDiagonalTailChunk000Sub001Block019Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block019Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block019Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block019Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block019Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block019Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block019HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block019Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block019Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part000
    + surrogateDiagTailX0RatChunk000Sub001Block019Part001
    + surrogateDiagTailX0RatChunk000Sub001Block019Part002
    + surrogateDiagTailX0RatChunk000Sub001Block019Part003
    + surrogateDiagTailX0RatChunk000Sub001Block019Part004
    + surrogateDiagTailX0RatChunk000Sub001Block019Part005
    + surrogateDiagTailX0RatChunk000Sub001Block019Part006
    + surrogateDiagTailX0RatChunk000Sub001Block019Part007
    + surrogateDiagTailX0RatChunk000Sub001Block019Part008
    + surrogateDiagTailX0RatChunk000Sub001Block019Part009

def surrogateDiagonalTailChunk000Sub001Block019MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block019Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block019Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part010
    + surrogateDiagTailX0RatChunk000Sub001Block019Part011
    + surrogateDiagTailX0RatChunk000Sub001Block019Part012
    + surrogateDiagTailX0RatChunk000Sub001Block019Part013
    + surrogateDiagTailX0RatChunk000Sub001Block019Part014
    + surrogateDiagTailX0RatChunk000Sub001Block019Part015
    + surrogateDiagTailX0RatChunk000Sub001Block019Part016
    + surrogateDiagTailX0RatChunk000Sub001Block019Part017
    + surrogateDiagTailX0RatChunk000Sub001Block019Part018
    + surrogateDiagTailX0RatChunk000Sub001Block019Part019

def surrogateDiagonalTailChunk000Sub001Block019TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block019Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block019Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block019Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part020
    + surrogateDiagTailX0RatChunk000Sub001Block019Part021
    + surrogateDiagTailX0RatChunk000Sub001Block019Part022
    + surrogateDiagTailX0RatChunk000Sub001Block019Part023
    + surrogateDiagTailX0RatChunk000Sub001Block019Part024

def surrogateDiagonalTailChunk000Sub001Block019Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block019HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block019MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block019TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block019 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block019Part000
    + surrogateDiagTailX0RatChunk000Sub001Block019Part001
    + surrogateDiagTailX0RatChunk000Sub001Block019Part002
    + surrogateDiagTailX0RatChunk000Sub001Block019Part003
    + surrogateDiagTailX0RatChunk000Sub001Block019Part004
    + surrogateDiagTailX0RatChunk000Sub001Block019Part005
    + surrogateDiagTailX0RatChunk000Sub001Block019Part006
    + surrogateDiagTailX0RatChunk000Sub001Block019Part007
    + surrogateDiagTailX0RatChunk000Sub001Block019Part008
    + surrogateDiagTailX0RatChunk000Sub001Block019Part009
    + surrogateDiagTailX0RatChunk000Sub001Block019Part010
    + surrogateDiagTailX0RatChunk000Sub001Block019Part011
    + surrogateDiagTailX0RatChunk000Sub001Block019Part012
    + surrogateDiagTailX0RatChunk000Sub001Block019Part013
    + surrogateDiagTailX0RatChunk000Sub001Block019Part014
    + surrogateDiagTailX0RatChunk000Sub001Block019Part015
    + surrogateDiagTailX0RatChunk000Sub001Block019Part016
    + surrogateDiagTailX0RatChunk000Sub001Block019Part017
    + surrogateDiagTailX0RatChunk000Sub001Block019Part018
    + surrogateDiagTailX0RatChunk000Sub001Block019Part019
    + surrogateDiagTailX0RatChunk000Sub001Block019Part020
    + surrogateDiagTailX0RatChunk000Sub001Block019Part021
    + surrogateDiagTailX0RatChunk000Sub001Block019Part022
    + surrogateDiagTailX0RatChunk000Sub001Block019Part023
    + surrogateDiagTailX0RatChunk000Sub001Block019Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block019_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block019Head + surrogateDiagTailX0RatChunk000Sub001Block019Mid + surrogateDiagTailX0RatChunk000Sub001Block019Tail =
      surrogateDiagTailX0RatChunk000Sub001Block019 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block019Head surrogateDiagTailX0RatChunk000Sub001Block019Mid surrogateDiagTailX0RatChunk000Sub001Block019Tail surrogateDiagTailX0RatChunk000Sub001Block019
  ring

def SurrogateDiagonalTailChunk000Sub001Block019HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block019HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block019Head

def SurrogateDiagonalTailChunk000Sub001Block019MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block019MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block019Mid

def SurrogateDiagonalTailChunk000Sub001Block019TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block019TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block019Tail

theorem surrogateDiagonalTailChunk000Sub001Block019_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block019HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block019MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block019TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block019Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block019 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block019HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block019MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block019TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block019Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block019_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
