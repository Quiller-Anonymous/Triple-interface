import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [150,160). -/

/-- Block 150 covers tail-support indices [8750,8775) and q from 14449 to 14489. -/

def TailChunk000Sub001Block150Part000SupportExplicit : Finset ℕ :=
  ([14449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14449
    = surrogateDiagTailX0RatChunk000Sub001Block150Part000

theorem surrogateDiagonalTailChunk000Sub001Block150Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part000] using hcert

def TailChunk000Sub001Block150Part001SupportExplicit : Finset ℕ :=
  ([14451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part001 : ℚ :=
  (51794323825 : ℚ) / 768660781628522496

def SurrogateDiagonalTailChunk000Sub001Block150Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14451
    = surrogateDiagTailX0RatChunk000Sub001Block150Part001

theorem surrogateDiagonalTailChunk000Sub001Block150Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part001] using hcert

def TailChunk000Sub001Block150Part002SupportExplicit : Finset ℕ :=
  ([14453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part002 : ℚ :=
  (25498091675 : ℚ) / 33965451961083887616

def SurrogateDiagonalTailChunk000Sub001Block150Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14453
    = surrogateDiagTailX0RatChunk000Sub001Block150Part002

theorem surrogateDiagonalTailChunk000Sub001Block150Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part002] using hcert

def TailChunk000Sub001Block150Part003SupportExplicit : Finset ℕ :=
  ([14457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part003 : ℚ :=
  (258399305 : ℚ) / 3411989822472192

def SurrogateDiagonalTailChunk000Sub001Block150Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14457
    = surrogateDiagTailX0RatChunk000Sub001Block150Part003

theorem surrogateDiagonalTailChunk000Sub001Block150Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part003] using hcert

def TailChunk000Sub001Block150Part004SupportExplicit : Finset ℕ :=
  ([14458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14458
    = surrogateDiagTailX0RatChunk000Sub001Block150Part004

theorem surrogateDiagonalTailChunk000Sub001Block150Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part004] using hcert

def TailChunk000Sub001Block150Part005SupportExplicit : Finset ℕ :=
  ([14459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part005 : ℚ :=
  (177604637 : ℚ) / 70058564666671104

def SurrogateDiagonalTailChunk000Sub001Block150Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14459
    = surrogateDiagTailX0RatChunk000Sub001Block150Part005

theorem surrogateDiagonalTailChunk000Sub001Block150Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part005] using hcert

def TailChunk000Sub001Block150Part006SupportExplicit : Finset ℕ :=
  ([14461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14461
    = surrogateDiagTailX0RatChunk000Sub001Block150Part006

theorem surrogateDiagonalTailChunk000Sub001Block150Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part006] using hcert

def TailChunk000Sub001Block150Part007SupportExplicit : Finset ℕ :=
  ([14462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part007 : ℚ :=
  (267970705525 : ℚ) / 3675789641592373248

def SurrogateDiagonalTailChunk000Sub001Block150Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14462
    = surrogateDiagTailX0RatChunk000Sub001Block150Part007

theorem surrogateDiagonalTailChunk000Sub001Block150Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part007] using hcert

def TailChunk000Sub001Block150Part008SupportExplicit : Finset ℕ :=
  ([14465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part008 : ℚ :=
  (16009034547 : ℚ) / 402170976917094400

def SurrogateDiagonalTailChunk000Sub001Block150Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14465
    = surrogateDiagTailX0RatChunk000Sub001Block150Part008

theorem surrogateDiagonalTailChunk000Sub001Block150Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part008] using hcert

def TailChunk000Sub001Block150Part009SupportExplicit : Finset ℕ :=
  ([14466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part009 : ℚ :=
  (14529843629 : ℚ) / 26992617932097600

def SurrogateDiagonalTailChunk000Sub001Block150Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14466
    = surrogateDiagTailX0RatChunk000Sub001Block150Part009

theorem surrogateDiagonalTailChunk000Sub001Block150Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part009] using hcert

def TailChunk000Sub001Block150Part010SupportExplicit : Finset ℕ :=
  ([14467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part010 : ℚ :=
  (57997540025 : ℚ) / 7164155543936827392

def SurrogateDiagonalTailChunk000Sub001Block150Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14467
    = surrogateDiagTailX0RatChunk000Sub001Block150Part010

theorem surrogateDiagonalTailChunk000Sub001Block150Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part010] using hcert

def TailChunk000Sub001Block150Part011SupportExplicit : Finset ℕ :=
  ([14469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part011 : ℚ :=
  (81262081175 : ℚ) / 436734697276440576

def SurrogateDiagonalTailChunk000Sub001Block150Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14469
    = surrogateDiagTailX0RatChunk000Sub001Block150Part011

theorem surrogateDiagonalTailChunk000Sub001Block150Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part011] using hcert

def TailChunk000Sub001Block150Part012SupportExplicit : Finset ℕ :=
  ([14470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part012 : ℚ :=
  (49142529275 : ℚ) / 349824328399984896

def SurrogateDiagonalTailChunk000Sub001Block150Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14470
    = surrogateDiagTailX0RatChunk000Sub001Block150Part012

theorem surrogateDiagonalTailChunk000Sub001Block150Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part012] using hcert

def TailChunk000Sub001Block150Part013SupportExplicit : Finset ℕ :=
  ([14471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part013 : ℚ :=
  (54484934075 : ℚ) / 31510485929800636416

def SurrogateDiagonalTailChunk000Sub001Block150Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14471
    = surrogateDiagTailX0RatChunk000Sub001Block150Part013

theorem surrogateDiagonalTailChunk000Sub001Block150Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part013] using hcert

def TailChunk000Sub001Block150Part014SupportExplicit : Finset ℕ :=
  ([14473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part014 : ℚ :=
  (1206388309 : ℚ) / 982737385999564800

def SurrogateDiagonalTailChunk000Sub001Block150Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14473
    = surrogateDiagTailX0RatChunk000Sub001Block150Part014

theorem surrogateDiagonalTailChunk000Sub001Block150Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part014] using hcert

def TailChunk000Sub001Block150Part015SupportExplicit : Finset ℕ :=
  ([14474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14474
    = surrogateDiagTailX0RatChunk000Sub001Block150Part015

theorem surrogateDiagonalTailChunk000Sub001Block150Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part015] using hcert

def TailChunk000Sub001Block150Part016SupportExplicit : Finset ℕ :=
  ([14477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part016 : ℚ :=
  (1055706443 : ℚ) / 636743155702507200

def SurrogateDiagonalTailChunk000Sub001Block150Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14477
    = surrogateDiagTailX0RatChunk000Sub001Block150Part016

theorem surrogateDiagonalTailChunk000Sub001Block150Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part016] using hcert

def TailChunk000Sub001Block150Part017SupportExplicit : Finset ℕ :=
  ([14478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part017 : ℚ :=
  (236300675 : ℚ) / 342911786563584

def SurrogateDiagonalTailChunk000Sub001Block150Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14478
    = surrogateDiagTailX0RatChunk000Sub001Block150Part017

theorem surrogateDiagonalTailChunk000Sub001Block150Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part017] using hcert

def TailChunk000Sub001Block150Part018SupportExplicit : Finset ℕ :=
  ([14479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14479
    = surrogateDiagTailX0RatChunk000Sub001Block150Part018

theorem surrogateDiagonalTailChunk000Sub001Block150Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part018] using hcert

def TailChunk000Sub001Block150Part019SupportExplicit : Finset ℕ :=
  ([14482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part019 : ℚ :=
  (177362837275 : ℚ) / 4955083865762070528

def SurrogateDiagonalTailChunk000Sub001Block150Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14482
    = surrogateDiagTailX0RatChunk000Sub001Block150Part019

theorem surrogateDiagonalTailChunk000Sub001Block150Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part019] using hcert

def TailChunk000Sub001Block150Part020SupportExplicit : Finset ℕ :=
  ([14483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part020 : ℚ :=
  (44634493225 : ℚ) / 3292770733189825536

def SurrogateDiagonalTailChunk000Sub001Block150Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14483
    = surrogateDiagTailX0RatChunk000Sub001Block150Part020

theorem surrogateDiagonalTailChunk000Sub001Block150Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part020] using hcert

def TailChunk000Sub001Block150Part021SupportExplicit : Finset ℕ :=
  ([14485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part021 : ℚ :=
  (1049392585525 : ℚ) / 45025760226802925568

def SurrogateDiagonalTailChunk000Sub001Block150Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14485
    = surrogateDiagTailX0RatChunk000Sub001Block150Part021

theorem surrogateDiagonalTailChunk000Sub001Block150Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part021] using hcert

def TailChunk000Sub001Block150Part022SupportExplicit : Finset ℕ :=
  ([14486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14486
    = surrogateDiagTailX0RatChunk000Sub001Block150Part022

theorem surrogateDiagonalTailChunk000Sub001Block150Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part022] using hcert

def TailChunk000Sub001Block150Part023SupportExplicit : Finset ℕ :=
  ([14487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part023 : ℚ :=
  (1481058391 : ℚ) / 14724592464026880

def SurrogateDiagonalTailChunk000Sub001Block150Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14487
    = surrogateDiagTailX0RatChunk000Sub001Block150Part023

theorem surrogateDiagonalTailChunk000Sub001Block150Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part023] using hcert

def TailChunk000Sub001Block150Part024SupportExplicit : Finset ℕ :=
  ([14489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block150Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block150Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14489
    = surrogateDiagTailX0RatChunk000Sub001Block150Part024

theorem surrogateDiagonalTailChunk000Sub001Block150Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block150Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block150Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block150Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block150Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block150Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block150Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block150HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block150Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block150Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block150Part000
    + surrogateDiagTailX0RatChunk000Sub001Block150Part001
    + surrogateDiagTailX0RatChunk000Sub001Block150Part002
    + surrogateDiagTailX0RatChunk000Sub001Block150Part003
    + surrogateDiagTailX0RatChunk000Sub001Block150Part004
    + surrogateDiagTailX0RatChunk000Sub001Block150Part005
    + surrogateDiagTailX0RatChunk000Sub001Block150Part006
    + surrogateDiagTailX0RatChunk000Sub001Block150Part007
    + surrogateDiagTailX0RatChunk000Sub001Block150Part008
    + surrogateDiagTailX0RatChunk000Sub001Block150Part009

def surrogateDiagonalTailChunk000Sub001Block150MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block150Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block150Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block150Part010
    + surrogateDiagTailX0RatChunk000Sub001Block150Part011
    + surrogateDiagTailX0RatChunk000Sub001Block150Part012
    + surrogateDiagTailX0RatChunk000Sub001Block150Part013
    + surrogateDiagTailX0RatChunk000Sub001Block150Part014
    + surrogateDiagTailX0RatChunk000Sub001Block150Part015
    + surrogateDiagTailX0RatChunk000Sub001Block150Part016
    + surrogateDiagTailX0RatChunk000Sub001Block150Part017
    + surrogateDiagTailX0RatChunk000Sub001Block150Part018
    + surrogateDiagTailX0RatChunk000Sub001Block150Part019

def surrogateDiagonalTailChunk000Sub001Block150TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block150Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block150Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block150Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block150Part020
    + surrogateDiagTailX0RatChunk000Sub001Block150Part021
    + surrogateDiagTailX0RatChunk000Sub001Block150Part022
    + surrogateDiagTailX0RatChunk000Sub001Block150Part023
    + surrogateDiagTailX0RatChunk000Sub001Block150Part024

def surrogateDiagonalTailChunk000Sub001Block150Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block150HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block150MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block150TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block150 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block150Part000
    + surrogateDiagTailX0RatChunk000Sub001Block150Part001
    + surrogateDiagTailX0RatChunk000Sub001Block150Part002
    + surrogateDiagTailX0RatChunk000Sub001Block150Part003
    + surrogateDiagTailX0RatChunk000Sub001Block150Part004
    + surrogateDiagTailX0RatChunk000Sub001Block150Part005
    + surrogateDiagTailX0RatChunk000Sub001Block150Part006
    + surrogateDiagTailX0RatChunk000Sub001Block150Part007
    + surrogateDiagTailX0RatChunk000Sub001Block150Part008
    + surrogateDiagTailX0RatChunk000Sub001Block150Part009
    + surrogateDiagTailX0RatChunk000Sub001Block150Part010
    + surrogateDiagTailX0RatChunk000Sub001Block150Part011
    + surrogateDiagTailX0RatChunk000Sub001Block150Part012
    + surrogateDiagTailX0RatChunk000Sub001Block150Part013
    + surrogateDiagTailX0RatChunk000Sub001Block150Part014
    + surrogateDiagTailX0RatChunk000Sub001Block150Part015
    + surrogateDiagTailX0RatChunk000Sub001Block150Part016
    + surrogateDiagTailX0RatChunk000Sub001Block150Part017
    + surrogateDiagTailX0RatChunk000Sub001Block150Part018
    + surrogateDiagTailX0RatChunk000Sub001Block150Part019
    + surrogateDiagTailX0RatChunk000Sub001Block150Part020
    + surrogateDiagTailX0RatChunk000Sub001Block150Part021
    + surrogateDiagTailX0RatChunk000Sub001Block150Part022
    + surrogateDiagTailX0RatChunk000Sub001Block150Part023
    + surrogateDiagTailX0RatChunk000Sub001Block150Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block150_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block150Head + surrogateDiagTailX0RatChunk000Sub001Block150Mid + surrogateDiagTailX0RatChunk000Sub001Block150Tail =
      surrogateDiagTailX0RatChunk000Sub001Block150 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block150Head surrogateDiagTailX0RatChunk000Sub001Block150Mid surrogateDiagTailX0RatChunk000Sub001Block150Tail surrogateDiagTailX0RatChunk000Sub001Block150
  ring

def SurrogateDiagonalTailChunk000Sub001Block150HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block150HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block150Head

def SurrogateDiagonalTailChunk000Sub001Block150MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block150MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block150Mid

def SurrogateDiagonalTailChunk000Sub001Block150TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block150TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block150Tail

theorem surrogateDiagonalTailChunk000Sub001Block150_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block150HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block150MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block150TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block150Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block150 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block150HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block150MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block150TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block150Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block150_eq_head_add_mid_add_tail

/-- Block 151 covers tail-support indices [8775,8800) and q from 14491 to 14529. -/

def TailChunk000Sub001Block151Part000SupportExplicit : Finset ℕ :=
  ([14491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part000 : ℚ :=
  (1099482925 : ℚ) / 918242467727671296

def SurrogateDiagonalTailChunk000Sub001Block151Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14491
    = surrogateDiagTailX0RatChunk000Sub001Block151Part000

theorem surrogateDiagonalTailChunk000Sub001Block151Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part000] using hcert

def TailChunk000Sub001Block151Part001SupportExplicit : Finset ℕ :=
  ([14493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part001 : ℚ :=
  (833532181 : ℚ) / 12442203948000960

def SurrogateDiagonalTailChunk000Sub001Block151Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14493
    = surrogateDiagTailX0RatChunk000Sub001Block151Part001

theorem surrogateDiagonalTailChunk000Sub001Block151Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part001] using hcert

def TailChunk000Sub001Block151Part002SupportExplicit : Finset ℕ :=
  ([14494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part002 : ℚ :=
  (820609515625 : ℚ) / 1723297215771459282

def SurrogateDiagonalTailChunk000Sub001Block151Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14494
    = surrogateDiagTailX0RatChunk000Sub001Block151Part002

theorem surrogateDiagonalTailChunk000Sub001Block151Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part002] using hcert

def TailChunk000Sub001Block151Part003SupportExplicit : Finset ℕ :=
  ([14495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part003 : ℚ :=
  (574197970475 : ℚ) / 16120321926842548224

def SurrogateDiagonalTailChunk000Sub001Block151Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14495
    = surrogateDiagTailX0RatChunk000Sub001Block151Part003

theorem surrogateDiagonalTailChunk000Sub001Block151Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part003] using hcert

def TailChunk000Sub001Block151Part004SupportExplicit : Finset ℕ :=
  ([14497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part004 : ℚ :=
  (76755707725 : ℚ) / 5142501100899827712

def SurrogateDiagonalTailChunk000Sub001Block151Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14497
    = surrogateDiagTailX0RatChunk000Sub001Block151Part004

theorem surrogateDiagonalTailChunk000Sub001Block151Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part004] using hcert

def TailChunk000Sub001Block151Part005SupportExplicit : Finset ℕ :=
  ([14498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part005 : ℚ :=
  (115963959679 : ℚ) / 187495316861059200

def SurrogateDiagonalTailChunk000Sub001Block151Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14498
    = surrogateDiagTailX0RatChunk000Sub001Block151Part005

theorem surrogateDiagonalTailChunk000Sub001Block151Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part005] using hcert

def TailChunk000Sub001Block151Part006SupportExplicit : Finset ℕ :=
  ([14501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part006 : ℚ :=
  (15385567475 : ℚ) / 4797253445763465216

def SurrogateDiagonalTailChunk000Sub001Block151Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14501
    = surrogateDiagTailX0RatChunk000Sub001Block151Part006

theorem surrogateDiagonalTailChunk000Sub001Block151Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part006] using hcert

def TailChunk000Sub001Block151Part007SupportExplicit : Finset ℕ :=
  ([14502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part007 : ℚ :=
  (912498364925 : ℚ) / 681560739833708544

def SurrogateDiagonalTailChunk000Sub001Block151Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14502
    = surrogateDiagTailX0RatChunk000Sub001Block151Part007

theorem surrogateDiagonalTailChunk000Sub001Block151Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part007] using hcert

def TailChunk000Sub001Block151Part008SupportExplicit : Finset ℕ :=
  ([14503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block151Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14503
    = surrogateDiagTailX0RatChunk000Sub001Block151Part008

theorem surrogateDiagonalTailChunk000Sub001Block151Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part008] using hcert

def TailChunk000Sub001Block151Part009SupportExplicit : Finset ℕ :=
  ([14505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part009 : ℚ :=
  (189845179325 : ℚ) / 1114821473740886016

def SurrogateDiagonalTailChunk000Sub001Block151Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14505
    = surrogateDiagTailX0RatChunk000Sub001Block151Part009

theorem surrogateDiagonalTailChunk000Sub001Block151Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part009] using hcert

def TailChunk000Sub001Block151Part010SupportExplicit : Finset ℕ :=
  ([14506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part010 : ℚ :=
  (821968890625 : ℚ) / 1729012166400382752

def SurrogateDiagonalTailChunk000Sub001Block151Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14506
    = surrogateDiagTailX0RatChunk000Sub001Block151Part010

theorem surrogateDiagonalTailChunk000Sub001Block151Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part010] using hcert

def TailChunk000Sub001Block151Part011SupportExplicit : Finset ℕ :=
  ([14507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part011 : ℚ :=
  (39215120375 : ℚ) / 51640163661367885824

def SurrogateDiagonalTailChunk000Sub001Block151Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14507
    = surrogateDiagTailX0RatChunk000Sub001Block151Part011

theorem surrogateDiagonalTailChunk000Sub001Block151Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part011] using hcert

def TailChunk000Sub001Block151Part012SupportExplicit : Finset ℕ :=
  ([14509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part012 : ℚ :=
  (13148323447 : ℚ) / 3018203311334275200

def SurrogateDiagonalTailChunk000Sub001Block151Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14509
    = surrogateDiagTailX0RatChunk000Sub001Block151Part012

theorem surrogateDiagonalTailChunk000Sub001Block151Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part012] using hcert

def TailChunk000Sub001Block151Part013SupportExplicit : Finset ℕ :=
  ([14510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part013 : ℚ :=
  (6246104959 : ℚ) / 7074224562000000

def SurrogateDiagonalTailChunk000Sub001Block151Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14510
    = surrogateDiagTailX0RatChunk000Sub001Block151Part013

theorem surrogateDiagonalTailChunk000Sub001Block151Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part013] using hcert

def TailChunk000Sub001Block151Part014SupportExplicit : Finset ℕ :=
  ([14511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part014 : ℚ :=
  (6364966301 : ℚ) / 52235491793356800

def SurrogateDiagonalTailChunk000Sub001Block151Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14511
    = surrogateDiagTailX0RatChunk000Sub001Block151Part014

theorem surrogateDiagonalTailChunk000Sub001Block151Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part014] using hcert

def TailChunk000Sub001Block151Part015SupportExplicit : Finset ℕ :=
  ([14513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part015 : ℚ :=
  (410073089 : ℚ) / 184548183857120160

def SurrogateDiagonalTailChunk000Sub001Block151Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14513
    = surrogateDiagTailX0RatChunk000Sub001Block151Part015

theorem surrogateDiagonalTailChunk000Sub001Block151Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part015] using hcert

def TailChunk000Sub001Block151Part016SupportExplicit : Finset ℕ :=
  ([14514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part016 : ℚ :=
  (34833772223 : ℚ) / 23180819044761600

def SurrogateDiagonalTailChunk000Sub001Block151Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14514
    = surrogateDiagTailX0RatChunk000Sub001Block151Part016

theorem surrogateDiagonalTailChunk000Sub001Block151Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part016] using hcert

def TailChunk000Sub001Block151Part017SupportExplicit : Finset ℕ :=
  ([14515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part017 : ℚ :=
  (175867024875 : ℚ) / 15133354371328546816

def SurrogateDiagonalTailChunk000Sub001Block151Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14515
    = surrogateDiagTailX0RatChunk000Sub001Block151Part017

theorem surrogateDiagonalTailChunk000Sub001Block151Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part017] using hcert

def TailChunk000Sub001Block151Part018SupportExplicit : Finset ℕ :=
  ([14518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part018 : ℚ :=
  (5950686949 : ℚ) / 6881083077427200

def SurrogateDiagonalTailChunk000Sub001Block151Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14518
    = surrogateDiagTailX0RatChunk000Sub001Block151Part018

theorem surrogateDiagonalTailChunk000Sub001Block151Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part018] using hcert

def TailChunk000Sub001Block151Part019SupportExplicit : Finset ℕ :=
  ([14519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block151Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14519
    = surrogateDiagTailX0RatChunk000Sub001Block151Part019

theorem surrogateDiagonalTailChunk000Sub001Block151Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part019] using hcert

def TailChunk000Sub001Block151Part020SupportExplicit : Finset ℕ :=
  ([14521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part020 : ℚ :=
  (43627368625 : ℚ) / 8936472269177782272

def SurrogateDiagonalTailChunk000Sub001Block151Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14521
    = surrogateDiagTailX0RatChunk000Sub001Block151Part020

theorem surrogateDiagonalTailChunk000Sub001Block151Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part020] using hcert

def TailChunk000Sub001Block151Part021SupportExplicit : Finset ℕ :=
  ([14522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part021 : ℚ :=
  (3184208889025 : ℚ) / 6254547093831548928

def SurrogateDiagonalTailChunk000Sub001Block151Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14522
    = surrogateDiagTailX0RatChunk000Sub001Block151Part021

theorem surrogateDiagonalTailChunk000Sub001Block151Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part021] using hcert

def TailChunk000Sub001Block151Part022SupportExplicit : Finset ℕ :=
  ([14523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part022 : ℚ :=
  (754160075 : ℚ) / 9974303863907072

def SurrogateDiagonalTailChunk000Sub001Block151Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14523
    = surrogateDiagTailX0RatChunk000Sub001Block151Part022

theorem surrogateDiagonalTailChunk000Sub001Block151Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part022] using hcert

def TailChunk000Sub001Block151Part023SupportExplicit : Finset ℕ :=
  ([14527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part023 : ℚ :=
  (38249275 : ℚ) / 47419801341935616

def SurrogateDiagonalTailChunk000Sub001Block151Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14527
    = surrogateDiagTailX0RatChunk000Sub001Block151Part023

theorem surrogateDiagonalTailChunk000Sub001Block151Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part023] using hcert

def TailChunk000Sub001Block151Part024SupportExplicit : Finset ℕ :=
  ([14529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block151Part024 : ℚ :=
  (91397974075 : ℚ) / 1167055034437060608

def SurrogateDiagonalTailChunk000Sub001Block151Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14529
    = surrogateDiagTailX0RatChunk000Sub001Block151Part024

theorem surrogateDiagonalTailChunk000Sub001Block151Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block151Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block151Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block151Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block151Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block151Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block151Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block151HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block151Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block151Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block151Part000
    + surrogateDiagTailX0RatChunk000Sub001Block151Part001
    + surrogateDiagTailX0RatChunk000Sub001Block151Part002
    + surrogateDiagTailX0RatChunk000Sub001Block151Part003
    + surrogateDiagTailX0RatChunk000Sub001Block151Part004
    + surrogateDiagTailX0RatChunk000Sub001Block151Part005
    + surrogateDiagTailX0RatChunk000Sub001Block151Part006
    + surrogateDiagTailX0RatChunk000Sub001Block151Part007
    + surrogateDiagTailX0RatChunk000Sub001Block151Part008
    + surrogateDiagTailX0RatChunk000Sub001Block151Part009

def surrogateDiagonalTailChunk000Sub001Block151MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block151Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block151Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block151Part010
    + surrogateDiagTailX0RatChunk000Sub001Block151Part011
    + surrogateDiagTailX0RatChunk000Sub001Block151Part012
    + surrogateDiagTailX0RatChunk000Sub001Block151Part013
    + surrogateDiagTailX0RatChunk000Sub001Block151Part014
    + surrogateDiagTailX0RatChunk000Sub001Block151Part015
    + surrogateDiagTailX0RatChunk000Sub001Block151Part016
    + surrogateDiagTailX0RatChunk000Sub001Block151Part017
    + surrogateDiagTailX0RatChunk000Sub001Block151Part018
    + surrogateDiagTailX0RatChunk000Sub001Block151Part019

def surrogateDiagonalTailChunk000Sub001Block151TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block151Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block151Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block151Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block151Part020
    + surrogateDiagTailX0RatChunk000Sub001Block151Part021
    + surrogateDiagTailX0RatChunk000Sub001Block151Part022
    + surrogateDiagTailX0RatChunk000Sub001Block151Part023
    + surrogateDiagTailX0RatChunk000Sub001Block151Part024

def surrogateDiagonalTailChunk000Sub001Block151Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block151HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block151MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block151TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block151 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block151Part000
    + surrogateDiagTailX0RatChunk000Sub001Block151Part001
    + surrogateDiagTailX0RatChunk000Sub001Block151Part002
    + surrogateDiagTailX0RatChunk000Sub001Block151Part003
    + surrogateDiagTailX0RatChunk000Sub001Block151Part004
    + surrogateDiagTailX0RatChunk000Sub001Block151Part005
    + surrogateDiagTailX0RatChunk000Sub001Block151Part006
    + surrogateDiagTailX0RatChunk000Sub001Block151Part007
    + surrogateDiagTailX0RatChunk000Sub001Block151Part008
    + surrogateDiagTailX0RatChunk000Sub001Block151Part009
    + surrogateDiagTailX0RatChunk000Sub001Block151Part010
    + surrogateDiagTailX0RatChunk000Sub001Block151Part011
    + surrogateDiagTailX0RatChunk000Sub001Block151Part012
    + surrogateDiagTailX0RatChunk000Sub001Block151Part013
    + surrogateDiagTailX0RatChunk000Sub001Block151Part014
    + surrogateDiagTailX0RatChunk000Sub001Block151Part015
    + surrogateDiagTailX0RatChunk000Sub001Block151Part016
    + surrogateDiagTailX0RatChunk000Sub001Block151Part017
    + surrogateDiagTailX0RatChunk000Sub001Block151Part018
    + surrogateDiagTailX0RatChunk000Sub001Block151Part019
    + surrogateDiagTailX0RatChunk000Sub001Block151Part020
    + surrogateDiagTailX0RatChunk000Sub001Block151Part021
    + surrogateDiagTailX0RatChunk000Sub001Block151Part022
    + surrogateDiagTailX0RatChunk000Sub001Block151Part023
    + surrogateDiagTailX0RatChunk000Sub001Block151Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block151_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block151Head + surrogateDiagTailX0RatChunk000Sub001Block151Mid + surrogateDiagTailX0RatChunk000Sub001Block151Tail =
      surrogateDiagTailX0RatChunk000Sub001Block151 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block151Head surrogateDiagTailX0RatChunk000Sub001Block151Mid surrogateDiagTailX0RatChunk000Sub001Block151Tail surrogateDiagTailX0RatChunk000Sub001Block151
  ring

def SurrogateDiagonalTailChunk000Sub001Block151HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block151HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block151Head

def SurrogateDiagonalTailChunk000Sub001Block151MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block151MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block151Mid

def SurrogateDiagonalTailChunk000Sub001Block151TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block151TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block151Tail

theorem surrogateDiagonalTailChunk000Sub001Block151_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block151HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block151MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block151TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block151Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block151 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block151HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block151MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block151TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block151Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block151_eq_head_add_mid_add_tail

/-- Block 152 covers tail-support indices [8800,8825) and q from 14530 to 14569. -/

def TailChunk000Sub001Block152Part000SupportExplicit : Finset ℕ :=
  ([14530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part000 : ℚ :=
  (2373461223325 : ℚ) / 2845334237163061248

def SurrogateDiagonalTailChunk000Sub001Block152Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14530
    = surrogateDiagTailX0RatChunk000Sub001Block152Part000

theorem surrogateDiagonalTailChunk000Sub001Block152Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part000] using hcert

def TailChunk000Sub001Block152Part001SupportExplicit : Finset ℕ :=
  ([14531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part001 : ℚ :=
  (17538633349 : ℚ) / 3036564951552000000

def SurrogateDiagonalTailChunk000Sub001Block152Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14531
    = surrogateDiagTailX0RatChunk000Sub001Block152Part001

theorem surrogateDiagonalTailChunk000Sub001Block152Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part001] using hcert

def TailChunk000Sub001Block152Part002SupportExplicit : Finset ℕ :=
  ([14533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14533
    = surrogateDiagTailX0RatChunk000Sub001Block152Part002

theorem surrogateDiagonalTailChunk000Sub001Block152Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part002] using hcert

def TailChunk000Sub001Block152Part003SupportExplicit : Finset ℕ :=
  ([14537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14537
    = surrogateDiagTailX0RatChunk000Sub001Block152Part003

theorem surrogateDiagonalTailChunk000Sub001Block152Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part003] using hcert

def TailChunk000Sub001Block152Part004SupportExplicit : Finset ℕ :=
  ([14538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part004 : ℚ :=
  (458517357775 : ℚ) / 344178236833550112

def SurrogateDiagonalTailChunk000Sub001Block152Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14538
    = surrogateDiagTailX0RatChunk000Sub001Block152Part004

theorem surrogateDiagonalTailChunk000Sub001Block152Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part004] using hcert

def TailChunk000Sub001Block152Part005SupportExplicit : Finset ℕ :=
  ([14539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part005 : ℚ :=
  (36226685767 : ℚ) / 1992290264713267200

def SurrogateDiagonalTailChunk000Sub001Block152Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14539
    = surrogateDiagTailX0RatChunk000Sub001Block152Part005

theorem surrogateDiagonalTailChunk000Sub001Block152Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part005] using hcert

def TailChunk000Sub001Block152Part006SupportExplicit : Finset ℕ :=
  ([14541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part006 : ℚ :=
  (58737193579 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk000Sub001Block152Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14541
    = surrogateDiagTailX0RatChunk000Sub001Block152Part006

theorem surrogateDiagonalTailChunk000Sub001Block152Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part006] using hcert

def TailChunk000Sub001Block152Part007SupportExplicit : Finset ℕ :=
  ([14542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part007 : ℚ :=
  (350237809 : ℚ) / 575106998400000

def SurrogateDiagonalTailChunk000Sub001Block152Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14542
    = surrogateDiagTailX0RatChunk000Sub001Block152Part007

theorem surrogateDiagonalTailChunk000Sub001Block152Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part007] using hcert

def TailChunk000Sub001Block152Part008SupportExplicit : Finset ℕ :=
  ([14543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14543
    = surrogateDiagTailX0RatChunk000Sub001Block152Part008

theorem surrogateDiagonalTailChunk000Sub001Block152Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part008] using hcert

def TailChunk000Sub001Block152Part009SupportExplicit : Finset ℕ :=
  ([14545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part009 : ℚ :=
  (1058096840725 : ℚ) / 45776694873582501888

def SurrogateDiagonalTailChunk000Sub001Block152Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14545
    = surrogateDiagTailX0RatChunk000Sub001Block152Part009

theorem surrogateDiagonalTailChunk000Sub001Block152Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part009] using hcert

def TailChunk000Sub001Block152Part010SupportExplicit : Finset ℕ :=
  ([14546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part010 : ℚ :=
  (2695966901875 : ℚ) / 3762021510812032128

def SurrogateDiagonalTailChunk000Sub001Block152Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14546
    = surrogateDiagTailX0RatChunk000Sub001Block152Part010

theorem surrogateDiagonalTailChunk000Sub001Block152Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part010] using hcert

def TailChunk000Sub001Block152Part011SupportExplicit : Finset ℕ :=
  ([14547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part011 : ℚ :=
  (1486374184225 : ℚ) / 15887061811871612928

def SurrogateDiagonalTailChunk000Sub001Block152Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14547
    = surrogateDiagTailX0RatChunk000Sub001Block152Part011

theorem surrogateDiagonalTailChunk000Sub001Block152Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part011] using hcert

def TailChunk000Sub001Block152Part012SupportExplicit : Finset ℕ :=
  ([14549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14549
    = surrogateDiagTailX0RatChunk000Sub001Block152Part012

theorem surrogateDiagonalTailChunk000Sub001Block152Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part012] using hcert

def TailChunk000Sub001Block152Part013SupportExplicit : Finset ℕ :=
  ([14551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14551
    = surrogateDiagTailX0RatChunk000Sub001Block152Part013

theorem surrogateDiagonalTailChunk000Sub001Block152Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part013] using hcert

def TailChunk000Sub001Block152Part014SupportExplicit : Finset ℕ :=
  ([14554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part014 : ℚ :=
  (3070552635925 : ℚ) / 5589466157070914688

def SurrogateDiagonalTailChunk000Sub001Block152Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14554
    = surrogateDiagTailX0RatChunk000Sub001Block152Part014

theorem surrogateDiagonalTailChunk000Sub001Block152Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part014] using hcert

def TailChunk000Sub001Block152Part015SupportExplicit : Finset ℕ :=
  ([14555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part015 : ℚ :=
  (371384199 : ℚ) / 13115283865600000

def SurrogateDiagonalTailChunk000Sub001Block152Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14555
    = surrogateDiagTailX0RatChunk000Sub001Block152Part015

theorem surrogateDiagonalTailChunk000Sub001Block152Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part015] using hcert

def TailChunk000Sub001Block152Part016SupportExplicit : Finset ℕ :=
  ([14557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14557
    = surrogateDiagTailX0RatChunk000Sub001Block152Part016

theorem surrogateDiagonalTailChunk000Sub001Block152Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part016] using hcert

def TailChunk000Sub001Block152Part017SupportExplicit : Finset ℕ :=
  ([14558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part017 : ℚ :=
  (41893878891 : ℚ) / 80049340000000000

def SurrogateDiagonalTailChunk000Sub001Block152Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14558
    = surrogateDiagTailX0RatChunk000Sub001Block152Part017

theorem surrogateDiagonalTailChunk000Sub001Block152Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part017] using hcert

def TailChunk000Sub001Block152Part018SupportExplicit : Finset ℕ :=
  ([14559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part018 : ℚ :=
  (187585487 : ℚ) / 2314537285294080

def SurrogateDiagonalTailChunk000Sub001Block152Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14559
    = surrogateDiagTailX0RatChunk000Sub001Block152Part018

theorem surrogateDiagonalTailChunk000Sub001Block152Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part018] using hcert

def TailChunk000Sub001Block152Part019SupportExplicit : Finset ℕ :=
  ([14561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14561
    = surrogateDiagTailX0RatChunk000Sub001Block152Part019

theorem surrogateDiagonalTailChunk000Sub001Block152Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part019] using hcert

def TailChunk000Sub001Block152Part020SupportExplicit : Finset ℕ :=
  ([14563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block152Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14563
    = surrogateDiagTailX0RatChunk000Sub001Block152Part020

theorem surrogateDiagonalTailChunk000Sub001Block152Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part020] using hcert

def TailChunk000Sub001Block152Part021SupportExplicit : Finset ℕ :=
  ([14565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part021 : ℚ :=
  (2471678347 : ℚ) / 9067211454074880

def SurrogateDiagonalTailChunk000Sub001Block152Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14565
    = surrogateDiagTailX0RatChunk000Sub001Block152Part021

theorem surrogateDiagonalTailChunk000Sub001Block152Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part021] using hcert

def TailChunk000Sub001Block152Part022SupportExplicit : Finset ℕ :=
  ([14566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part022 : ℚ :=
  (828782640625 : ℚ) / 1757800428269306322

def SurrogateDiagonalTailChunk000Sub001Block152Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14566
    = surrogateDiagTailX0RatChunk000Sub001Block152Part022

theorem surrogateDiagonalTailChunk000Sub001Block152Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part022] using hcert

def TailChunk000Sub001Block152Part023SupportExplicit : Finset ℕ :=
  ([14567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part023 : ℚ :=
  (10851332627 : ℚ) / 1213151936879001600

def SurrogateDiagonalTailChunk000Sub001Block152Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14567
    = surrogateDiagTailX0RatChunk000Sub001Block152Part023

theorem surrogateDiagonalTailChunk000Sub001Block152Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part023] using hcert

def TailChunk000Sub001Block152Part024SupportExplicit : Finset ℕ :=
  ([14569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block152Part024 : ℚ :=
  (46583275125 : ℚ) / 14663937395511001088

def SurrogateDiagonalTailChunk000Sub001Block152Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14569
    = surrogateDiagTailX0RatChunk000Sub001Block152Part024

theorem surrogateDiagonalTailChunk000Sub001Block152Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block152Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block152Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block152Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block152Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block152Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block152Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block152HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block152Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block152Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block152Part000
    + surrogateDiagTailX0RatChunk000Sub001Block152Part001
    + surrogateDiagTailX0RatChunk000Sub001Block152Part002
    + surrogateDiagTailX0RatChunk000Sub001Block152Part003
    + surrogateDiagTailX0RatChunk000Sub001Block152Part004
    + surrogateDiagTailX0RatChunk000Sub001Block152Part005
    + surrogateDiagTailX0RatChunk000Sub001Block152Part006
    + surrogateDiagTailX0RatChunk000Sub001Block152Part007
    + surrogateDiagTailX0RatChunk000Sub001Block152Part008
    + surrogateDiagTailX0RatChunk000Sub001Block152Part009

def surrogateDiagonalTailChunk000Sub001Block152MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block152Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block152Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block152Part010
    + surrogateDiagTailX0RatChunk000Sub001Block152Part011
    + surrogateDiagTailX0RatChunk000Sub001Block152Part012
    + surrogateDiagTailX0RatChunk000Sub001Block152Part013
    + surrogateDiagTailX0RatChunk000Sub001Block152Part014
    + surrogateDiagTailX0RatChunk000Sub001Block152Part015
    + surrogateDiagTailX0RatChunk000Sub001Block152Part016
    + surrogateDiagTailX0RatChunk000Sub001Block152Part017
    + surrogateDiagTailX0RatChunk000Sub001Block152Part018
    + surrogateDiagTailX0RatChunk000Sub001Block152Part019

def surrogateDiagonalTailChunk000Sub001Block152TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block152Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block152Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block152Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block152Part020
    + surrogateDiagTailX0RatChunk000Sub001Block152Part021
    + surrogateDiagTailX0RatChunk000Sub001Block152Part022
    + surrogateDiagTailX0RatChunk000Sub001Block152Part023
    + surrogateDiagTailX0RatChunk000Sub001Block152Part024

def surrogateDiagonalTailChunk000Sub001Block152Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block152HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block152MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block152TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block152 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block152Part000
    + surrogateDiagTailX0RatChunk000Sub001Block152Part001
    + surrogateDiagTailX0RatChunk000Sub001Block152Part002
    + surrogateDiagTailX0RatChunk000Sub001Block152Part003
    + surrogateDiagTailX0RatChunk000Sub001Block152Part004
    + surrogateDiagTailX0RatChunk000Sub001Block152Part005
    + surrogateDiagTailX0RatChunk000Sub001Block152Part006
    + surrogateDiagTailX0RatChunk000Sub001Block152Part007
    + surrogateDiagTailX0RatChunk000Sub001Block152Part008
    + surrogateDiagTailX0RatChunk000Sub001Block152Part009
    + surrogateDiagTailX0RatChunk000Sub001Block152Part010
    + surrogateDiagTailX0RatChunk000Sub001Block152Part011
    + surrogateDiagTailX0RatChunk000Sub001Block152Part012
    + surrogateDiagTailX0RatChunk000Sub001Block152Part013
    + surrogateDiagTailX0RatChunk000Sub001Block152Part014
    + surrogateDiagTailX0RatChunk000Sub001Block152Part015
    + surrogateDiagTailX0RatChunk000Sub001Block152Part016
    + surrogateDiagTailX0RatChunk000Sub001Block152Part017
    + surrogateDiagTailX0RatChunk000Sub001Block152Part018
    + surrogateDiagTailX0RatChunk000Sub001Block152Part019
    + surrogateDiagTailX0RatChunk000Sub001Block152Part020
    + surrogateDiagTailX0RatChunk000Sub001Block152Part021
    + surrogateDiagTailX0RatChunk000Sub001Block152Part022
    + surrogateDiagTailX0RatChunk000Sub001Block152Part023
    + surrogateDiagTailX0RatChunk000Sub001Block152Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block152_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block152Head + surrogateDiagTailX0RatChunk000Sub001Block152Mid + surrogateDiagTailX0RatChunk000Sub001Block152Tail =
      surrogateDiagTailX0RatChunk000Sub001Block152 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block152Head surrogateDiagTailX0RatChunk000Sub001Block152Mid surrogateDiagTailX0RatChunk000Sub001Block152Tail surrogateDiagTailX0RatChunk000Sub001Block152
  ring

def SurrogateDiagonalTailChunk000Sub001Block152HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block152HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block152Head

def SurrogateDiagonalTailChunk000Sub001Block152MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block152MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block152Mid

def SurrogateDiagonalTailChunk000Sub001Block152TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block152TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block152Tail

theorem surrogateDiagonalTailChunk000Sub001Block152_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block152HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block152MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block152TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block152Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block152 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block152HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block152MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block152TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block152Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block152_eq_head_add_mid_add_tail

/-- Block 153 covers tail-support indices [8825,8850) and q from 14570 to 14610. -/

def TailChunk000Sub001Block153Part000SupportExplicit : Finset ℕ :=
  ([14570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part000 : ℚ :=
  (7443882451 : ℚ) / 7738591376793600

def SurrogateDiagonalTailChunk000Sub001Block153Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14570
    = surrogateDiagTailX0RatChunk000Sub001Block153Part000

theorem surrogateDiagonalTailChunk000Sub001Block153Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part000] using hcert

def TailChunk000Sub001Block153Part001SupportExplicit : Finset ℕ :=
  ([14573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part001 : ℚ :=
  (566453015875 : ℚ) / 61596188269835747328

def SurrogateDiagonalTailChunk000Sub001Block153Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14573
    = surrogateDiagTailX0RatChunk000Sub001Block153Part001

theorem surrogateDiagonalTailChunk000Sub001Block153Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part001] using hcert

def TailChunk000Sub001Block153Part002SupportExplicit : Finset ℕ :=
  ([14574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part002 : ℚ :=
  (768915540725 : ℚ) / 371557680080200704

def SurrogateDiagonalTailChunk000Sub001Block153Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14574
    = surrogateDiagTailX0RatChunk000Sub001Block153Part002

theorem surrogateDiagonalTailChunk000Sub001Block153Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part002] using hcert

def TailChunk000Sub001Block153Part003SupportExplicit : Finset ℕ :=
  ([14577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part003 : ℚ :=
  (211292267575 : ℚ) / 2798453234979569664

def SurrogateDiagonalTailChunk000Sub001Block153Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14577
    = surrogateDiagTailX0RatChunk000Sub001Block153Part003

theorem surrogateDiagonalTailChunk000Sub001Block153Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part003] using hcert

def TailChunk000Sub001Block153Part004SupportExplicit : Finset ℕ :=
  ([14578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part004 : ℚ :=
  (117816389225 : ℚ) / 229560616931917824

def SurrogateDiagonalTailChunk000Sub001Block153Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14578
    = surrogateDiagTailX0RatChunk000Sub001Block153Part004

theorem surrogateDiagonalTailChunk000Sub001Block153Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part004] using hcert

def TailChunk000Sub001Block153Part005SupportExplicit : Finset ℕ :=
  ([14579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part005 : ℚ :=
  (3571735009 : ℚ) / 4159103040133171200

def SurrogateDiagonalTailChunk000Sub001Block153Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14579
    = surrogateDiagTailX0RatChunk000Sub001Block153Part005

theorem surrogateDiagonalTailChunk000Sub001Block153Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part005] using hcert

def TailChunk000Sub001Block153Part006SupportExplicit : Finset ℕ :=
  ([14581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part006 : ℚ :=
  (271803461675 : ℚ) / 30445615998623721024

def SurrogateDiagonalTailChunk000Sub001Block153Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14581
    = surrogateDiagTailX0RatChunk000Sub001Block153Part006

theorem surrogateDiagonalTailChunk000Sub001Block153Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part006] using hcert

def TailChunk000Sub001Block153Part007SupportExplicit : Finset ℕ :=
  ([14582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part007 : ℚ :=
  (32517220575 : ℚ) / 60840766885139648

def SurrogateDiagonalTailChunk000Sub001Block153Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14582
    = surrogateDiagTailX0RatChunk000Sub001Block153Part007

theorem surrogateDiagonalTailChunk000Sub001Block153Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part007] using hcert

def TailChunk000Sub001Block153Part008SupportExplicit : Finset ℕ :=
  ([14583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part008 : ℚ :=
  (738425033 : ℚ) / 11159941625216640

def SurrogateDiagonalTailChunk000Sub001Block153Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14583
    = surrogateDiagTailX0RatChunk000Sub001Block153Part008

theorem surrogateDiagonalTailChunk000Sub001Block153Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part008] using hcert

def TailChunk000Sub001Block153Part009SupportExplicit : Finset ℕ :=
  ([14585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part009 : ℚ :=
  (354639891175 : ℚ) / 15427503302699483136

def SurrogateDiagonalTailChunk000Sub001Block153Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14585
    = surrogateDiagTailX0RatChunk000Sub001Block153Part009

theorem surrogateDiagonalTailChunk000Sub001Block153Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part009] using hcert

def TailChunk000Sub001Block153Part010SupportExplicit : Finset ℕ :=
  ([14586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part010 : ℚ :=
  (55965245563 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub001Block153Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14586
    = surrogateDiagTailX0RatChunk000Sub001Block153Part010

theorem surrogateDiagonalTailChunk000Sub001Block153Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part010] using hcert

def TailChunk000Sub001Block153Part011SupportExplicit : Finset ℕ :=
  ([14587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part011 : ℚ :=
  (10732635275 : ℚ) / 6971814401979743232

def SurrogateDiagonalTailChunk000Sub001Block153Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14587
    = surrogateDiagTailX0RatChunk000Sub001Block153Part011

theorem surrogateDiagonalTailChunk000Sub001Block153Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part011] using hcert

def TailChunk000Sub001Block153Part012SupportExplicit : Finset ℕ :=
  ([14590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part012 : ℚ :=
  (105253050775 : ℚ) / 120527369552339712

def SurrogateDiagonalTailChunk000Sub001Block153Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14590
    = surrogateDiagTailX0RatChunk000Sub001Block153Part012

theorem surrogateDiagonalTailChunk000Sub001Block153Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part012] using hcert

def TailChunk000Sub001Block153Part013SupportExplicit : Finset ℕ :=
  ([14591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block153Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14591
    = surrogateDiagTailX0RatChunk000Sub001Block153Part013

theorem surrogateDiagonalTailChunk000Sub001Block153Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part013] using hcert

def TailChunk000Sub001Block153Part014SupportExplicit : Finset ℕ :=
  ([14593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block153Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14593
    = surrogateDiagTailX0RatChunk000Sub001Block153Part014

theorem surrogateDiagonalTailChunk000Sub001Block153Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part014] using hcert

def TailChunk000Sub001Block153Part015SupportExplicit : Finset ℕ :=
  ([14594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part015 : ℚ :=
  (831972015625 : ℚ) / 1771357289349906432

def SurrogateDiagonalTailChunk000Sub001Block153Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14594
    = surrogateDiagTailX0RatChunk000Sub001Block153Part015

theorem surrogateDiagonalTailChunk000Sub001Block153Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part015] using hcert

def TailChunk000Sub001Block153Part016SupportExplicit : Finset ℕ :=
  ([14595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part016 : ℚ :=
  (27979867525 : ℚ) / 89148572660662272

def SurrogateDiagonalTailChunk000Sub001Block153Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14595
    = surrogateDiagTailX0RatChunk000Sub001Block153Part016

theorem surrogateDiagonalTailChunk000Sub001Block153Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part016] using hcert

def TailChunk000Sub001Block153Part017SupportExplicit : Finset ℕ :=
  ([14597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part017 : ℚ :=
  (17697297901 : ℚ) / 3092152799074435200

def SurrogateDiagonalTailChunk000Sub001Block153Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14597
    = surrogateDiagTailX0RatChunk000Sub001Block153Part017

theorem surrogateDiagonalTailChunk000Sub001Block153Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part017] using hcert

def TailChunk000Sub001Block153Part018SupportExplicit : Finset ℕ :=
  ([14599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part018 : ℚ :=
  (159142634825 : ℚ) / 41085944493609083904

def SurrogateDiagonalTailChunk000Sub001Block153Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14599
    = surrogateDiagTailX0RatChunk000Sub001Block153Part018

theorem surrogateDiagonalTailChunk000Sub001Block153Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part018] using hcert

def TailChunk000Sub001Block153Part019SupportExplicit : Finset ℕ :=
  ([14601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part019 : ℚ :=
  (507670091 : ℚ) / 6561518889369600

def SurrogateDiagonalTailChunk000Sub001Block153Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14601
    = surrogateDiagTailX0RatChunk000Sub001Block153Part019

theorem surrogateDiagonalTailChunk000Sub001Block153Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part019] using hcert

def TailChunk000Sub001Block153Part020SupportExplicit : Finset ℕ :=
  ([14603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part020 : ℚ :=
  (234865869025 : ℚ) / 88808787539227312128

def SurrogateDiagonalTailChunk000Sub001Block153Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14603
    = surrogateDiagTailX0RatChunk000Sub001Block153Part020

theorem surrogateDiagonalTailChunk000Sub001Block153Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part020] using hcert

def TailChunk000Sub001Block153Part021SupportExplicit : Finset ℕ :=
  ([14605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part021 : ℚ :=
  (332360809925 : ℚ) / 18897734026969104384

def SurrogateDiagonalTailChunk000Sub001Block153Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14605
    = surrogateDiagTailX0RatChunk000Sub001Block153Part021

theorem surrogateDiagonalTailChunk000Sub001Block153Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part021] using hcert

def TailChunk000Sub001Block153Part022SupportExplicit : Finset ℕ :=
  ([14606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part022 : ℚ :=
  (22426126325 : ℚ) / 44826530956048512

def SurrogateDiagonalTailChunk000Sub001Block153Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14606
    = surrogateDiagTailX0RatChunk000Sub001Block153Part022

theorem surrogateDiagonalTailChunk000Sub001Block153Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part022] using hcert

def TailChunk000Sub001Block153Part023SupportExplicit : Finset ℕ :=
  ([14609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part023 : ℚ :=
  (272845253375 : ℚ) / 30680263206758136384

def SurrogateDiagonalTailChunk000Sub001Block153Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14609
    = surrogateDiagTailX0RatChunk000Sub001Block153Part023

theorem surrogateDiagonalTailChunk000Sub001Block153Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part023] using hcert

def TailChunk000Sub001Block153Part024SupportExplicit : Finset ℕ :=
  ([14610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block153Part024 : ℚ :=
  (695158160675 : ℚ) / 285694505605545984

def SurrogateDiagonalTailChunk000Sub001Block153Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14610
    = surrogateDiagTailX0RatChunk000Sub001Block153Part024

theorem surrogateDiagonalTailChunk000Sub001Block153Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block153Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block153Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block153Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block153Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block153Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block153Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block153HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block153Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block153Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block153Part000
    + surrogateDiagTailX0RatChunk000Sub001Block153Part001
    + surrogateDiagTailX0RatChunk000Sub001Block153Part002
    + surrogateDiagTailX0RatChunk000Sub001Block153Part003
    + surrogateDiagTailX0RatChunk000Sub001Block153Part004
    + surrogateDiagTailX0RatChunk000Sub001Block153Part005
    + surrogateDiagTailX0RatChunk000Sub001Block153Part006
    + surrogateDiagTailX0RatChunk000Sub001Block153Part007
    + surrogateDiagTailX0RatChunk000Sub001Block153Part008
    + surrogateDiagTailX0RatChunk000Sub001Block153Part009

def surrogateDiagonalTailChunk000Sub001Block153MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block153Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block153Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block153Part010
    + surrogateDiagTailX0RatChunk000Sub001Block153Part011
    + surrogateDiagTailX0RatChunk000Sub001Block153Part012
    + surrogateDiagTailX0RatChunk000Sub001Block153Part013
    + surrogateDiagTailX0RatChunk000Sub001Block153Part014
    + surrogateDiagTailX0RatChunk000Sub001Block153Part015
    + surrogateDiagTailX0RatChunk000Sub001Block153Part016
    + surrogateDiagTailX0RatChunk000Sub001Block153Part017
    + surrogateDiagTailX0RatChunk000Sub001Block153Part018
    + surrogateDiagTailX0RatChunk000Sub001Block153Part019

def surrogateDiagonalTailChunk000Sub001Block153TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block153Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block153Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block153Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block153Part020
    + surrogateDiagTailX0RatChunk000Sub001Block153Part021
    + surrogateDiagTailX0RatChunk000Sub001Block153Part022
    + surrogateDiagTailX0RatChunk000Sub001Block153Part023
    + surrogateDiagTailX0RatChunk000Sub001Block153Part024

def surrogateDiagonalTailChunk000Sub001Block153Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block153HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block153MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block153TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block153 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block153Part000
    + surrogateDiagTailX0RatChunk000Sub001Block153Part001
    + surrogateDiagTailX0RatChunk000Sub001Block153Part002
    + surrogateDiagTailX0RatChunk000Sub001Block153Part003
    + surrogateDiagTailX0RatChunk000Sub001Block153Part004
    + surrogateDiagTailX0RatChunk000Sub001Block153Part005
    + surrogateDiagTailX0RatChunk000Sub001Block153Part006
    + surrogateDiagTailX0RatChunk000Sub001Block153Part007
    + surrogateDiagTailX0RatChunk000Sub001Block153Part008
    + surrogateDiagTailX0RatChunk000Sub001Block153Part009
    + surrogateDiagTailX0RatChunk000Sub001Block153Part010
    + surrogateDiagTailX0RatChunk000Sub001Block153Part011
    + surrogateDiagTailX0RatChunk000Sub001Block153Part012
    + surrogateDiagTailX0RatChunk000Sub001Block153Part013
    + surrogateDiagTailX0RatChunk000Sub001Block153Part014
    + surrogateDiagTailX0RatChunk000Sub001Block153Part015
    + surrogateDiagTailX0RatChunk000Sub001Block153Part016
    + surrogateDiagTailX0RatChunk000Sub001Block153Part017
    + surrogateDiagTailX0RatChunk000Sub001Block153Part018
    + surrogateDiagTailX0RatChunk000Sub001Block153Part019
    + surrogateDiagTailX0RatChunk000Sub001Block153Part020
    + surrogateDiagTailX0RatChunk000Sub001Block153Part021
    + surrogateDiagTailX0RatChunk000Sub001Block153Part022
    + surrogateDiagTailX0RatChunk000Sub001Block153Part023
    + surrogateDiagTailX0RatChunk000Sub001Block153Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block153_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block153Head + surrogateDiagTailX0RatChunk000Sub001Block153Mid + surrogateDiagTailX0RatChunk000Sub001Block153Tail =
      surrogateDiagTailX0RatChunk000Sub001Block153 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block153Head surrogateDiagTailX0RatChunk000Sub001Block153Mid surrogateDiagTailX0RatChunk000Sub001Block153Tail surrogateDiagTailX0RatChunk000Sub001Block153
  ring

def SurrogateDiagonalTailChunk000Sub001Block153HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block153HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block153Head

def SurrogateDiagonalTailChunk000Sub001Block153MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block153MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block153Mid

def SurrogateDiagonalTailChunk000Sub001Block153TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block153TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block153Tail

theorem surrogateDiagonalTailChunk000Sub001Block153_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block153HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block153MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block153TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block153Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block153 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block153HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block153MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block153TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block153Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block153_eq_head_add_mid_add_tail

/-- Block 154 covers tail-support indices [8850,8875) and q from 14611 to 14649. -/

def TailChunk000Sub001Block154Part000SupportExplicit : Finset ℕ :=
  ([14611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part000 : ℚ :=
  (113292604925 : ℚ) / 45659564381929734144

def SurrogateDiagonalTailChunk000Sub001Block154Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14611
    = surrogateDiagTailX0RatChunk000Sub001Block154Part000

theorem surrogateDiagonalTailChunk000Sub001Block154Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part000] using hcert

def TailChunk000Sub001Block154Part001SupportExplicit : Finset ℕ :=
  ([14613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part001 : ℚ :=
  (5931725263 : ℚ) / 90016615020659520

def SurrogateDiagonalTailChunk000Sub001Block154Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14613
    = surrogateDiagTailX0RatChunk000Sub001Block154Part001

theorem surrogateDiagonalTailChunk000Sub001Block154Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part001] using hcert

def TailChunk000Sub001Block154Part002SupportExplicit : Finset ℕ :=
  ([14614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part002 : ℚ :=
  (834253890625 : ℚ) / 1781088662095928562

def SurrogateDiagonalTailChunk000Sub001Block154Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14614
    = surrogateDiagTailX0RatChunk000Sub001Block154Part002

theorem surrogateDiagonalTailChunk000Sub001Block154Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part002] using hcert

def TailChunk000Sub001Block154Part003SupportExplicit : Finset ℕ :=
  ([14615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part003 : ℚ :=
  (635397166075 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk000Sub001Block154Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14615
    = surrogateDiagTailX0RatChunk000Sub001Block154Part003

theorem surrogateDiagonalTailChunk000Sub001Block154Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part003] using hcert

def TailChunk000Sub001Block154Part004SupportExplicit : Finset ℕ :=
  ([14617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part004 : ℚ :=
  (4405534963 : ℚ) / 4135851647504515200

def SurrogateDiagonalTailChunk000Sub001Block154Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14617
    = surrogateDiagTailX0RatChunk000Sub001Block154Part004

theorem surrogateDiagonalTailChunk000Sub001Block154Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part004] using hcert

def TailChunk000Sub001Block154Part005SupportExplicit : Finset ℕ :=
  ([14618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part005 : ℚ :=
  (834710640625 : ℚ) / 1783039738086849312

def SurrogateDiagonalTailChunk000Sub001Block154Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14618
    = surrogateDiagTailX0RatChunk000Sub001Block154Part005

theorem surrogateDiagonalTailChunk000Sub001Block154Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part005] using hcert

def TailChunk000Sub001Block154Part006SupportExplicit : Finset ℕ :=
  ([14619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part006 : ℚ :=
  (1824207881 : ℚ) / 19087362957249600

def SurrogateDiagonalTailChunk000Sub001Block154Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14619
    = surrogateDiagTailX0RatChunk000Sub001Block154Part006

theorem surrogateDiagonalTailChunk000Sub001Block154Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part006] using hcert

def TailChunk000Sub001Block154Part007SupportExplicit : Finset ℕ :=
  ([14621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block154Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14621
    = surrogateDiagTailX0RatChunk000Sub001Block154Part007

theorem surrogateDiagonalTailChunk000Sub001Block154Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part007] using hcert

def TailChunk000Sub001Block154Part008SupportExplicit : Finset ℕ :=
  ([14622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part008 : ℚ :=
  (927663290675 : ℚ) / 704410760725668864

def SurrogateDiagonalTailChunk000Sub001Block154Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14622
    = surrogateDiagTailX0RatChunk000Sub001Block154Part008

theorem surrogateDiagonalTailChunk000Sub001Block154Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part008] using hcert

def TailChunk000Sub001Block154Part009SupportExplicit : Finset ℕ :=
  ([14623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part009 : ℚ :=
  (273366899075 : ℚ) / 30798094134917873664

def SurrogateDiagonalTailChunk000Sub001Block154Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14623
    = surrogateDiagTailX0RatChunk000Sub001Block154Part009

theorem surrogateDiagonalTailChunk000Sub001Block154Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part009] using hcert

def TailChunk000Sub001Block154Part010SupportExplicit : Finset ℕ :=
  ([14626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part010 : ℚ :=
  (7197330877 : ℚ) / 14441330000462400

def SurrogateDiagonalTailChunk000Sub001Block154Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14626
    = surrogateDiagTailX0RatChunk000Sub001Block154Part010

theorem surrogateDiagonalTailChunk000Sub001Block154Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part010] using hcert

def TailChunk000Sub001Block154Part011SupportExplicit : Finset ℕ :=
  ([14627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block154Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14627
    = surrogateDiagTailX0RatChunk000Sub001Block154Part011

theorem surrogateDiagonalTailChunk000Sub001Block154Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part011] using hcert

def TailChunk000Sub001Block154Part012SupportExplicit : Finset ℕ :=
  ([14629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block154Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14629
    = surrogateDiagTailX0RatChunk000Sub001Block154Part012

theorem surrogateDiagonalTailChunk000Sub001Block154Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part012] using hcert

def TailChunk000Sub001Block154Part013SupportExplicit : Finset ℕ :=
  ([14630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part013 : ℚ :=
  (23123986127 : ℚ) / 11611827693158400

def SurrogateDiagonalTailChunk000Sub001Block154Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14630
    = surrogateDiagTailX0RatChunk000Sub001Block154Part013

theorem surrogateDiagonalTailChunk000Sub001Block154Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part013] using hcert

def TailChunk000Sub001Block154Part014SupportExplicit : Finset ℕ :=
  ([14631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part014 : ℚ :=
  (23227907275 : ℚ) / 353363473526352672

def SurrogateDiagonalTailChunk000Sub001Block154Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14631
    = surrogateDiagTailX0RatChunk000Sub001Block154Part014

theorem surrogateDiagonalTailChunk000Sub001Block154Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part014] using hcert

def TailChunk000Sub001Block154Part015SupportExplicit : Finset ℕ :=
  ([14633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block154Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14633
    = surrogateDiagTailX0RatChunk000Sub001Block154Part015

theorem surrogateDiagonalTailChunk000Sub001Block154Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part015] using hcert

def TailChunk000Sub001Block154Part016SupportExplicit : Finset ℕ :=
  ([14635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part016 : ℚ :=
  (1071220710025 : ℚ) / 46920659886614857728

def SurrogateDiagonalTailChunk000Sub001Block154Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14635
    = surrogateDiagTailX0RatChunk000Sub001Block154Part016

theorem surrogateDiagonalTailChunk000Sub001Block154Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part016] using hcert

def TailChunk000Sub001Block154Part017SupportExplicit : Finset ℕ :=
  ([14637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part017 : ℚ :=
  (2118291491 : ℚ) / 12887478868377600

def SurrogateDiagonalTailChunk000Sub001Block154Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14637
    = surrogateDiagTailX0RatChunk000Sub001Block154Part017

theorem surrogateDiagonalTailChunk000Sub001Block154Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part017] using hcert

def TailChunk000Sub001Block154Part018SupportExplicit : Finset ℕ :=
  ([14638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part018 : ℚ :=
  (10090831825 : ℚ) / 323278723584793728

def SurrogateDiagonalTailChunk000Sub001Block154Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14638
    = surrogateDiagTailX0RatChunk000Sub001Block154Part018

theorem surrogateDiagonalTailChunk000Sub001Block154Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part018] using hcert

def TailChunk000Sub001Block154Part019SupportExplicit : Finset ℕ :=
  ([14639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block154Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14639
    = surrogateDiagTailX0RatChunk000Sub001Block154Part019

theorem surrogateDiagonalTailChunk000Sub001Block154Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part019] using hcert

def TailChunk000Sub001Block154Part020SupportExplicit : Finset ℕ :=
  ([14642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block154Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14642
    = surrogateDiagTailX0RatChunk000Sub001Block154Part020

theorem surrogateDiagonalTailChunk000Sub001Block154Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part020] using hcert

def TailChunk000Sub001Block154Part021SupportExplicit : Finset ℕ :=
  ([14645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part021 : ℚ :=
  (379357911 : ℚ) / 13115283865600000

def SurrogateDiagonalTailChunk000Sub001Block154Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14645
    = surrogateDiagTailX0RatChunk000Sub001Block154Part021

theorem surrogateDiagonalTailChunk000Sub001Block154Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part021] using hcert

def TailChunk000Sub001Block154Part022SupportExplicit : Finset ℕ :=
  ([14646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part022 : ℚ :=
  (244156079 : ℚ) / 464950059417600

def SurrogateDiagonalTailChunk000Sub001Block154Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14646
    = surrogateDiagTailX0RatChunk000Sub001Block154Part022

theorem surrogateDiagonalTailChunk000Sub001Block154Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part022] using hcert

def TailChunk000Sub001Block154Part023SupportExplicit : Finset ℕ :=
  ([14647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part023 : ℚ :=
  (1527301493 : ℚ) / 2150338461696000000

def SurrogateDiagonalTailChunk000Sub001Block154Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14647
    = surrogateDiagTailX0RatChunk000Sub001Block154Part023

theorem surrogateDiagonalTailChunk000Sub001Block154Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part023] using hcert

def TailChunk000Sub001Block154Part024SupportExplicit : Finset ℕ :=
  ([14649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block154Part024 : ℚ :=
  (1485828897475 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk000Sub001Block154Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14649
    = surrogateDiagTailX0RatChunk000Sub001Block154Part024

theorem surrogateDiagonalTailChunk000Sub001Block154Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block154Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block154Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block154Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block154Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block154Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block154Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block154HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block154Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block154Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block154Part000
    + surrogateDiagTailX0RatChunk000Sub001Block154Part001
    + surrogateDiagTailX0RatChunk000Sub001Block154Part002
    + surrogateDiagTailX0RatChunk000Sub001Block154Part003
    + surrogateDiagTailX0RatChunk000Sub001Block154Part004
    + surrogateDiagTailX0RatChunk000Sub001Block154Part005
    + surrogateDiagTailX0RatChunk000Sub001Block154Part006
    + surrogateDiagTailX0RatChunk000Sub001Block154Part007
    + surrogateDiagTailX0RatChunk000Sub001Block154Part008
    + surrogateDiagTailX0RatChunk000Sub001Block154Part009

def surrogateDiagonalTailChunk000Sub001Block154MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block154Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block154Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block154Part010
    + surrogateDiagTailX0RatChunk000Sub001Block154Part011
    + surrogateDiagTailX0RatChunk000Sub001Block154Part012
    + surrogateDiagTailX0RatChunk000Sub001Block154Part013
    + surrogateDiagTailX0RatChunk000Sub001Block154Part014
    + surrogateDiagTailX0RatChunk000Sub001Block154Part015
    + surrogateDiagTailX0RatChunk000Sub001Block154Part016
    + surrogateDiagTailX0RatChunk000Sub001Block154Part017
    + surrogateDiagTailX0RatChunk000Sub001Block154Part018
    + surrogateDiagTailX0RatChunk000Sub001Block154Part019

def surrogateDiagonalTailChunk000Sub001Block154TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block154Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block154Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block154Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block154Part020
    + surrogateDiagTailX0RatChunk000Sub001Block154Part021
    + surrogateDiagTailX0RatChunk000Sub001Block154Part022
    + surrogateDiagTailX0RatChunk000Sub001Block154Part023
    + surrogateDiagTailX0RatChunk000Sub001Block154Part024

def surrogateDiagonalTailChunk000Sub001Block154Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block154HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block154MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block154TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block154 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block154Part000
    + surrogateDiagTailX0RatChunk000Sub001Block154Part001
    + surrogateDiagTailX0RatChunk000Sub001Block154Part002
    + surrogateDiagTailX0RatChunk000Sub001Block154Part003
    + surrogateDiagTailX0RatChunk000Sub001Block154Part004
    + surrogateDiagTailX0RatChunk000Sub001Block154Part005
    + surrogateDiagTailX0RatChunk000Sub001Block154Part006
    + surrogateDiagTailX0RatChunk000Sub001Block154Part007
    + surrogateDiagTailX0RatChunk000Sub001Block154Part008
    + surrogateDiagTailX0RatChunk000Sub001Block154Part009
    + surrogateDiagTailX0RatChunk000Sub001Block154Part010
    + surrogateDiagTailX0RatChunk000Sub001Block154Part011
    + surrogateDiagTailX0RatChunk000Sub001Block154Part012
    + surrogateDiagTailX0RatChunk000Sub001Block154Part013
    + surrogateDiagTailX0RatChunk000Sub001Block154Part014
    + surrogateDiagTailX0RatChunk000Sub001Block154Part015
    + surrogateDiagTailX0RatChunk000Sub001Block154Part016
    + surrogateDiagTailX0RatChunk000Sub001Block154Part017
    + surrogateDiagTailX0RatChunk000Sub001Block154Part018
    + surrogateDiagTailX0RatChunk000Sub001Block154Part019
    + surrogateDiagTailX0RatChunk000Sub001Block154Part020
    + surrogateDiagTailX0RatChunk000Sub001Block154Part021
    + surrogateDiagTailX0RatChunk000Sub001Block154Part022
    + surrogateDiagTailX0RatChunk000Sub001Block154Part023
    + surrogateDiagTailX0RatChunk000Sub001Block154Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block154_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block154Head + surrogateDiagTailX0RatChunk000Sub001Block154Mid + surrogateDiagTailX0RatChunk000Sub001Block154Tail =
      surrogateDiagTailX0RatChunk000Sub001Block154 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block154Head surrogateDiagTailX0RatChunk000Sub001Block154Mid surrogateDiagTailX0RatChunk000Sub001Block154Tail surrogateDiagTailX0RatChunk000Sub001Block154
  ring

def SurrogateDiagonalTailChunk000Sub001Block154HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block154HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block154Head

def SurrogateDiagonalTailChunk000Sub001Block154MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block154MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block154Mid

def SurrogateDiagonalTailChunk000Sub001Block154TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block154TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block154Tail

theorem surrogateDiagonalTailChunk000Sub001Block154_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block154HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block154MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block154TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block154Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block154 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block154HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block154MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block154TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block154Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block154_eq_head_add_mid_add_tail

/-- Block 155 covers tail-support indices [8875,8900) and q from 14653 to 14690. -/

def TailChunk000Sub001Block155Part000SupportExplicit : Finset ℕ :=
  ([14653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block155Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14653
    = surrogateDiagTailX0RatChunk000Sub001Block155Part000

theorem surrogateDiagonalTailChunk000Sub001Block155Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part000] using hcert

def TailChunk000Sub001Block155Part001SupportExplicit : Finset ℕ :=
  ([14654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part001 : ℚ :=
  (329655163 : ℚ) / 14006209577779200

def SurrogateDiagonalTailChunk000Sub001Block155Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14654
    = surrogateDiagTailX0RatChunk000Sub001Block155Part001

theorem surrogateDiagonalTailChunk000Sub001Block155Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part001] using hcert

def TailChunk000Sub001Block155Part002SupportExplicit : Finset ℕ :=
  ([14655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part002 : ℚ :=
  (387579128275 : ℚ) / 2323411240916877312

def SurrogateDiagonalTailChunk000Sub001Block155Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14655
    = surrogateDiagTailX0RatChunk000Sub001Block155Part002

theorem surrogateDiagonalTailChunk000Sub001Block155Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part002] using hcert

def TailChunk000Sub001Block155Part003SupportExplicit : Finset ℕ :=
  ([14657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block155Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14657
    = surrogateDiagTailX0RatChunk000Sub001Block155Part003

theorem surrogateDiagonalTailChunk000Sub001Block155Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part003] using hcert

def TailChunk000Sub001Block155Part004SupportExplicit : Finset ℕ :=
  ([14658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part004 : ℚ :=
  (27884508775 : ℚ) / 28164695139385344

def SurrogateDiagonalTailChunk000Sub001Block155Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14658
    = surrogateDiagTailX0RatChunk000Sub001Block155Part004

theorem surrogateDiagonalTailChunk000Sub001Block155Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part004] using hcert

def TailChunk000Sub001Block155Part005SupportExplicit : Finset ℕ :=
  ([14659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part005 : ℚ :=
  (6314628075 : ℚ) / 8999631090670526464

def SurrogateDiagonalTailChunk000Sub001Block155Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14659
    = surrogateDiagTailX0RatChunk000Sub001Block155Part005

theorem surrogateDiagonalTailChunk000Sub001Block155Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part005] using hcert

def TailChunk000Sub001Block155Part006SupportExplicit : Finset ℕ :=
  ([14662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block155Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14662
    = surrogateDiagTailX0RatChunk000Sub001Block155Part006

theorem surrogateDiagonalTailChunk000Sub001Block155Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part006] using hcert

def TailChunk000Sub001Block155Part007SupportExplicit : Finset ℕ :=
  ([14663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part007 : ℚ :=
  (6788718787 : ℚ) / 840325951584000000

def SurrogateDiagonalTailChunk000Sub001Block155Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14663
    = surrogateDiagTailX0RatChunk000Sub001Block155Part007

theorem surrogateDiagonalTailChunk000Sub001Block155Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part007] using hcert

def TailChunk000Sub001Block155Part008SupportExplicit : Finset ℕ :=
  ([14665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part008 : ℚ :=
  (126728454575 : ℚ) / 2302418507934302208

def SurrogateDiagonalTailChunk000Sub001Block155Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14665
    = surrogateDiagTailX0RatChunk000Sub001Block155Part008

theorem surrogateDiagonalTailChunk000Sub001Block155Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part008] using hcert

def TailChunk000Sub001Block155Part009SupportExplicit : Finset ℕ :=
  ([14666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block155Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14666
    = surrogateDiagTailX0RatChunk000Sub001Block155Part009

theorem surrogateDiagonalTailChunk000Sub001Block155Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part009] using hcert

def TailChunk000Sub001Block155Part010SupportExplicit : Finset ℕ :=
  ([14667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part010 : ℚ :=
  (373477266325 : ℚ) / 5709678295236943872

def SurrogateDiagonalTailChunk000Sub001Block155Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14667
    = surrogateDiagTailX0RatChunk000Sub001Block155Part010

theorem surrogateDiagonalTailChunk000Sub001Block155Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part010] using hcert

def TailChunk000Sub001Block155Part011SupportExplicit : Finset ℕ :=
  ([14669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block155Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14669
    = surrogateDiagTailX0RatChunk000Sub001Block155Part011

theorem surrogateDiagonalTailChunk000Sub001Block155Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part011] using hcert

def TailChunk000Sub001Block155Part012SupportExplicit : Finset ℕ :=
  ([14671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part012 : ℚ :=
  (47226880425 : ℚ) / 15079418779325431808

def SurrogateDiagonalTailChunk000Sub001Block155Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14671
    = surrogateDiagTailX0RatChunk000Sub001Block155Part012

theorem surrogateDiagonalTailChunk000Sub001Block155Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part012] using hcert

def TailChunk000Sub001Block155Part013SupportExplicit : Finset ℕ :=
  ([14673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part013 : ℚ :=
  (1495626371425 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk000Sub001Block155Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14673
    = surrogateDiagTailX0RatChunk000Sub001Block155Part013

theorem surrogateDiagonalTailChunk000Sub001Block155Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part013] using hcert

def TailChunk000Sub001Block155Part014SupportExplicit : Finset ℕ :=
  ([14674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part014 : ℚ :=
  (1147223307 : ℚ) / 12001304442265600

def SurrogateDiagonalTailChunk000Sub001Block155Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14674
    = surrogateDiagTailX0RatChunk000Sub001Block155Part014

theorem surrogateDiagonalTailChunk000Sub001Block155Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part014] using hcert

def TailChunk000Sub001Block155Part015SupportExplicit : Finset ℕ :=
  ([14677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part015 : ℚ :=
  (44561619125 : ℚ) / 9327080653428621312

def SurrogateDiagonalTailChunk000Sub001Block155Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14677
    = surrogateDiagTailX0RatChunk000Sub001Block155Part015

theorem surrogateDiagonalTailChunk000Sub001Block155Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part015] using hcert

def TailChunk000Sub001Block155Part016SupportExplicit : Finset ℕ :=
  ([14678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part016 : ℚ :=
  (901995339 : ℚ) / 85681205859942400

def SurrogateDiagonalTailChunk000Sub001Block155Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14678
    = surrogateDiagTailX0RatChunk000Sub001Block155Part016

theorem surrogateDiagonalTailChunk000Sub001Block155Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part016] using hcert

def TailChunk000Sub001Block155Part017SupportExplicit : Finset ℕ :=
  ([14681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part017 : ℚ :=
  (25440976675 : ℚ) / 26522628997512241152

def SurrogateDiagonalTailChunk000Sub001Block155Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14681
    = surrogateDiagTailX0RatChunk000Sub001Block155Part017

theorem surrogateDiagonalTailChunk000Sub001Block155Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part017] using hcert

def TailChunk000Sub001Block155Part018SupportExplicit : Finset ℕ :=
  ([14682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part018 : ℚ :=
  (374169903725 : ℚ) / 716048858396572224

def SurrogateDiagonalTailChunk000Sub001Block155Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14682
    = surrogateDiagTailX0RatChunk000Sub001Block155Part018

theorem surrogateDiagonalTailChunk000Sub001Block155Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part018] using hcert

def TailChunk000Sub001Block155Part019SupportExplicit : Finset ℕ :=
  ([14683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block155Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14683
    = surrogateDiagTailX0RatChunk000Sub001Block155Part019

theorem surrogateDiagonalTailChunk000Sub001Block155Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part019] using hcert

def TailChunk000Sub001Block155Part020SupportExplicit : Finset ℕ :=
  ([14685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part020 : ℚ :=
  (26982410387 : ℚ) / 122842173249945600

def SurrogateDiagonalTailChunk000Sub001Block155Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14685
    = surrogateDiagTailX0RatChunk000Sub001Block155Part020

theorem surrogateDiagonalTailChunk000Sub001Block155Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part020] using hcert

def TailChunk000Sub001Block155Part021SupportExplicit : Finset ℕ :=
  ([14686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part021 : ℚ :=
  (344819661775 : ℚ) / 3909101895634157568

def SurrogateDiagonalTailChunk000Sub001Block155Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14686
    = surrogateDiagTailX0RatChunk000Sub001Block155Part021

theorem surrogateDiagonalTailChunk000Sub001Block155Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part021] using hcert

def TailChunk000Sub001Block155Part022SupportExplicit : Finset ℕ :=
  ([14687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part022 : ℚ :=
  (266052264775 : ℚ) / 93236525427874940928

def SurrogateDiagonalTailChunk000Sub001Block155Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14687
    = surrogateDiagTailX0RatChunk000Sub001Block155Part022

theorem surrogateDiagonalTailChunk000Sub001Block155Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part022] using hcert

def TailChunk000Sub001Block155Part023SupportExplicit : Finset ℕ :=
  ([14689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part023 : ℚ :=
  (6288493975 : ℚ) / 4694560332851625984

def SurrogateDiagonalTailChunk000Sub001Block155Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14689
    = surrogateDiagTailX0RatChunk000Sub001Block155Part023

theorem surrogateDiagonalTailChunk000Sub001Block155Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part023] using hcert

def TailChunk000Sub001Block155Part024SupportExplicit : Finset ℕ :=
  ([14690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block155Part024 : ℚ :=
  (492288843925 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub001Block155Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14690
    = surrogateDiagTailX0RatChunk000Sub001Block155Part024

theorem surrogateDiagonalTailChunk000Sub001Block155Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block155Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block155Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block155Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block155Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block155Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block155Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block155HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block155Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block155Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block155Part000
    + surrogateDiagTailX0RatChunk000Sub001Block155Part001
    + surrogateDiagTailX0RatChunk000Sub001Block155Part002
    + surrogateDiagTailX0RatChunk000Sub001Block155Part003
    + surrogateDiagTailX0RatChunk000Sub001Block155Part004
    + surrogateDiagTailX0RatChunk000Sub001Block155Part005
    + surrogateDiagTailX0RatChunk000Sub001Block155Part006
    + surrogateDiagTailX0RatChunk000Sub001Block155Part007
    + surrogateDiagTailX0RatChunk000Sub001Block155Part008
    + surrogateDiagTailX0RatChunk000Sub001Block155Part009

def surrogateDiagonalTailChunk000Sub001Block155MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block155Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block155Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block155Part010
    + surrogateDiagTailX0RatChunk000Sub001Block155Part011
    + surrogateDiagTailX0RatChunk000Sub001Block155Part012
    + surrogateDiagTailX0RatChunk000Sub001Block155Part013
    + surrogateDiagTailX0RatChunk000Sub001Block155Part014
    + surrogateDiagTailX0RatChunk000Sub001Block155Part015
    + surrogateDiagTailX0RatChunk000Sub001Block155Part016
    + surrogateDiagTailX0RatChunk000Sub001Block155Part017
    + surrogateDiagTailX0RatChunk000Sub001Block155Part018
    + surrogateDiagTailX0RatChunk000Sub001Block155Part019

def surrogateDiagonalTailChunk000Sub001Block155TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block155Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block155Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block155Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block155Part020
    + surrogateDiagTailX0RatChunk000Sub001Block155Part021
    + surrogateDiagTailX0RatChunk000Sub001Block155Part022
    + surrogateDiagTailX0RatChunk000Sub001Block155Part023
    + surrogateDiagTailX0RatChunk000Sub001Block155Part024

def surrogateDiagonalTailChunk000Sub001Block155Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block155HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block155MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block155TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block155 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block155Part000
    + surrogateDiagTailX0RatChunk000Sub001Block155Part001
    + surrogateDiagTailX0RatChunk000Sub001Block155Part002
    + surrogateDiagTailX0RatChunk000Sub001Block155Part003
    + surrogateDiagTailX0RatChunk000Sub001Block155Part004
    + surrogateDiagTailX0RatChunk000Sub001Block155Part005
    + surrogateDiagTailX0RatChunk000Sub001Block155Part006
    + surrogateDiagTailX0RatChunk000Sub001Block155Part007
    + surrogateDiagTailX0RatChunk000Sub001Block155Part008
    + surrogateDiagTailX0RatChunk000Sub001Block155Part009
    + surrogateDiagTailX0RatChunk000Sub001Block155Part010
    + surrogateDiagTailX0RatChunk000Sub001Block155Part011
    + surrogateDiagTailX0RatChunk000Sub001Block155Part012
    + surrogateDiagTailX0RatChunk000Sub001Block155Part013
    + surrogateDiagTailX0RatChunk000Sub001Block155Part014
    + surrogateDiagTailX0RatChunk000Sub001Block155Part015
    + surrogateDiagTailX0RatChunk000Sub001Block155Part016
    + surrogateDiagTailX0RatChunk000Sub001Block155Part017
    + surrogateDiagTailX0RatChunk000Sub001Block155Part018
    + surrogateDiagTailX0RatChunk000Sub001Block155Part019
    + surrogateDiagTailX0RatChunk000Sub001Block155Part020
    + surrogateDiagTailX0RatChunk000Sub001Block155Part021
    + surrogateDiagTailX0RatChunk000Sub001Block155Part022
    + surrogateDiagTailX0RatChunk000Sub001Block155Part023
    + surrogateDiagTailX0RatChunk000Sub001Block155Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block155_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block155Head + surrogateDiagTailX0RatChunk000Sub001Block155Mid + surrogateDiagTailX0RatChunk000Sub001Block155Tail =
      surrogateDiagTailX0RatChunk000Sub001Block155 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block155Head surrogateDiagTailX0RatChunk000Sub001Block155Mid surrogateDiagTailX0RatChunk000Sub001Block155Tail surrogateDiagTailX0RatChunk000Sub001Block155
  ring

def SurrogateDiagonalTailChunk000Sub001Block155HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block155HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block155Head

def SurrogateDiagonalTailChunk000Sub001Block155MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block155MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block155Mid

def SurrogateDiagonalTailChunk000Sub001Block155TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block155TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block155Tail

theorem surrogateDiagonalTailChunk000Sub001Block155_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block155HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block155MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block155TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block155Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block155 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block155HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block155MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block155TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block155Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block155_eq_head_add_mid_add_tail

/-- Block 156 covers tail-support indices [8900,8925) and q from 14691 to 14730. -/

def TailChunk000Sub001Block156Part000SupportExplicit : Finset ℕ :=
  ([14691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part000 : ℚ :=
  (1500276117775 : ℚ) / 20469829501482682368

def SurrogateDiagonalTailChunk000Sub001Block156Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14691
    = surrogateDiagTailX0RatChunk000Sub001Block156Part000

theorem surrogateDiagonalTailChunk000Sub001Block156Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part000] using hcert

def TailChunk000Sub001Block156Part001SupportExplicit : Finset ℕ :=
  ([14693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part001 : ℚ :=
  (275982626075 : ℚ) / 31392348006120312384

def SurrogateDiagonalTailChunk000Sub001Block156Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14693
    = surrogateDiagTailX0RatChunk000Sub001Block156Part001

theorem surrogateDiagonalTailChunk000Sub001Block156Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part001] using hcert

def TailChunk000Sub001Block156Part002SupportExplicit : Finset ℕ :=
  ([14694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part002 : ℚ :=
  (222252089 : ℚ) / 355415606507520

def SurrogateDiagonalTailChunk000Sub001Block156Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14694
    = surrogateDiagTailX0RatChunk000Sub001Block156Part002

theorem surrogateDiagonalTailChunk000Sub001Block156Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part002] using hcert

def TailChunk000Sub001Block156Part003SupportExplicit : Finset ℕ :=
  ([14695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part003 : ℚ :=
  (180247023375 : ℚ) / 15898374951787534336

def SurrogateDiagonalTailChunk000Sub001Block156Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14695
    = surrogateDiagTailX0RatChunk000Sub001Block156Part003

theorem surrogateDiagonalTailChunk000Sub001Block156Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part003] using hcert

def TailChunk000Sub001Block156Part004SupportExplicit : Finset ℕ :=
  ([14698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block156Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14698
    = surrogateDiagTailX0RatChunk000Sub001Block156Part004

theorem surrogateDiagonalTailChunk000Sub001Block156Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part004] using hcert

def TailChunk000Sub001Block156Part005SupportExplicit : Finset ℕ :=
  ([14699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block156Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14699
    = surrogateDiagTailX0RatChunk000Sub001Block156Part005

theorem surrogateDiagonalTailChunk000Sub001Block156Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part005] using hcert

def TailChunk000Sub001Block156Part006SupportExplicit : Finset ℕ :=
  ([14701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part006 : ℚ :=
  (3762187927 : ℚ) / 4300676923392000000

def SurrogateDiagonalTailChunk000Sub001Block156Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14701
    = surrogateDiagTailX0RatChunk000Sub001Block156Part006

theorem surrogateDiagonalTailChunk000Sub001Block156Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part006] using hcert

def TailChunk000Sub001Block156Part007SupportExplicit : Finset ℕ :=
  ([14702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block156Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14702
    = surrogateDiagTailX0RatChunk000Sub001Block156Part007

theorem surrogateDiagonalTailChunk000Sub001Block156Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part007] using hcert

def TailChunk000Sub001Block156Part008SupportExplicit : Finset ℕ :=
  ([14705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part008 : ℚ :=
  (227960892975 : ℚ) / 12238812678524502016

def SurrogateDiagonalTailChunk000Sub001Block156Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14705
    = surrogateDiagTailX0RatChunk000Sub001Block156Part008

theorem surrogateDiagonalTailChunk000Sub001Block156Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part008] using hcert

def TailChunk000Sub001Block156Part009SupportExplicit : Finset ℕ :=
  ([14707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part009 : ℚ :=
  (19737873827 : ℚ) / 93849886224000000

def SurrogateDiagonalTailChunk000Sub001Block156Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14707
    = surrogateDiagTailX0RatChunk000Sub001Block156Part009

theorem surrogateDiagonalTailChunk000Sub001Block156Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part009] using hcert

def TailChunk000Sub001Block156Part010SupportExplicit : Finset ℕ :=
  ([14709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part010 : ℚ :=
  (6008025509725 : ℚ) / 23101494110819814528

def SurrogateDiagonalTailChunk000Sub001Block156Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14709
    = surrogateDiagTailX0RatChunk000Sub001Block156Part010

theorem surrogateDiagonalTailChunk000Sub001Block156Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part010] using hcert

def TailChunk000Sub001Block156Part011SupportExplicit : Finset ℕ :=
  ([14710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part011 : ℚ :=
  (8559350417 : ℚ) / 9963568443225600

def SurrogateDiagonalTailChunk000Sub001Block156Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14710
    = surrogateDiagTailX0RatChunk000Sub001Block156Part011

theorem surrogateDiagonalTailChunk000Sub001Block156Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part011] using hcert

def TailChunk000Sub001Block156Part012SupportExplicit : Finset ℕ :=
  ([14711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part012 : ℚ :=
  (1622576202875 : ℚ) / 13261314498756120576

def SurrogateDiagonalTailChunk000Sub001Block156Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14711
    = surrogateDiagTailX0RatChunk000Sub001Block156Part012

theorem surrogateDiagonalTailChunk000Sub001Block156Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part012] using hcert

def TailChunk000Sub001Block156Part013SupportExplicit : Finset ℕ :=
  ([14713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part013 : ℚ :=
  (3382380765625 : ℚ) / 29285573448117883392

def SurrogateDiagonalTailChunk000Sub001Block156Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14713
    = surrogateDiagTailX0RatChunk000Sub001Block156Part013

theorem surrogateDiagonalTailChunk000Sub001Block156Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part013] using hcert

def TailChunk000Sub001Block156Part014SupportExplicit : Finset ℕ :=
  ([14714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part014 : ℚ :=
  (110344726963 : ℚ) / 157561115922000000

def SurrogateDiagonalTailChunk000Sub001Block156Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14714
    = surrogateDiagTailX0RatChunk000Sub001Block156Part014

theorem surrogateDiagonalTailChunk000Sub001Block156Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part014] using hcert

def TailChunk000Sub001Block156Part015SupportExplicit : Finset ℕ :=
  ([14717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part015 : ℚ :=
  (3384220140625 : ℚ) / 29317435894184853792

def SurrogateDiagonalTailChunk000Sub001Block156Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14717
    = surrogateDiagTailX0RatChunk000Sub001Block156Part015

theorem surrogateDiagonalTailChunk000Sub001Block156Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part015] using hcert

def TailChunk000Sub001Block156Part016SupportExplicit : Finset ℕ :=
  ([14718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part016 : ℚ :=
  (6654586861 : ℚ) / 3887037501649920

def SurrogateDiagonalTailChunk000Sub001Block156Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14718
    = surrogateDiagTailX0RatChunk000Sub001Block156Part016

theorem surrogateDiagonalTailChunk000Sub001Block156Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part016] using hcert

def TailChunk000Sub001Block156Part017SupportExplicit : Finset ℕ :=
  ([14719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part017 : ℚ :=
  (517373991067 : ℚ) / 4205899801133875200

def SurrogateDiagonalTailChunk000Sub001Block156Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14719
    = surrogateDiagTailX0RatChunk000Sub001Block156Part017

theorem surrogateDiagonalTailChunk000Sub001Block156Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part017] using hcert

def TailChunk000Sub001Block156Part018SupportExplicit : Finset ℕ :=
  ([14721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part018 : ℚ :=
  (2361141161 : ℚ) / 6147789312000000

def SurrogateDiagonalTailChunk000Sub001Block156Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14721
    = surrogateDiagTailX0RatChunk000Sub001Block156Part018

theorem surrogateDiagonalTailChunk000Sub001Block156Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part018] using hcert

def TailChunk000Sub001Block156Part019SupportExplicit : Finset ℕ :=
  ([14722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part019 : ℚ :=
  (779958650275 : ℚ) / 1426861386935304192

def SurrogateDiagonalTailChunk000Sub001Block156Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14722
    = surrogateDiagTailX0RatChunk000Sub001Block156Part019

theorem surrogateDiagonalTailChunk000Sub001Block156Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part019] using hcert

def TailChunk000Sub001Block156Part020SupportExplicit : Finset ℕ :=
  ([14723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part020 : ℚ :=
  (3386980140625 : ℚ) / 29365278303594872082

def SurrogateDiagonalTailChunk000Sub001Block156Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14723
    = surrogateDiagTailX0RatChunk000Sub001Block156Part020

theorem surrogateDiagonalTailChunk000Sub001Block156Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part020] using hcert

def TailChunk000Sub001Block156Part021SupportExplicit : Finset ℕ :=
  ([14726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part021 : ℚ :=
  (120224595625 : ℚ) / 239074831765592064

def SurrogateDiagonalTailChunk000Sub001Block156Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14726
    = surrogateDiagTailX0RatChunk000Sub001Block156Part021

theorem surrogateDiagonalTailChunk000Sub001Block156Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part021] using hcert

def TailChunk000Sub001Block156Part022SupportExplicit : Finset ℕ :=
  ([14727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part022 : ℚ :=
  (6022740509125 : ℚ) / 23214805947954874368

def SurrogateDiagonalTailChunk000Sub001Block156Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14727
    = surrogateDiagTailX0RatChunk000Sub001Block156Part022

theorem surrogateDiagonalTailChunk000Sub001Block156Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part022] using hcert

def TailChunk000Sub001Block156Part023SupportExplicit : Finset ℕ :=
  ([14729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part023 : ℚ :=
  (44016066433 : ℚ) / 249442248137932800

def SurrogateDiagonalTailChunk000Sub001Block156Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14729
    = surrogateDiagTailX0RatChunk000Sub001Block156Part023

theorem surrogateDiagonalTailChunk000Sub001Block156Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part023] using hcert

def TailChunk000Sub001Block156Part024SupportExplicit : Finset ℕ :=
  ([14730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block156Part024 : ℚ :=
  (28265102843 : ℚ) / 11808673710489600

def SurrogateDiagonalTailChunk000Sub001Block156Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14730
    = surrogateDiagTailX0RatChunk000Sub001Block156Part024

theorem surrogateDiagonalTailChunk000Sub001Block156Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block156Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block156Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block156Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block156Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block156Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block156Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block156HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block156Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block156Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block156Part000
    + surrogateDiagTailX0RatChunk000Sub001Block156Part001
    + surrogateDiagTailX0RatChunk000Sub001Block156Part002
    + surrogateDiagTailX0RatChunk000Sub001Block156Part003
    + surrogateDiagTailX0RatChunk000Sub001Block156Part004
    + surrogateDiagTailX0RatChunk000Sub001Block156Part005
    + surrogateDiagTailX0RatChunk000Sub001Block156Part006
    + surrogateDiagTailX0RatChunk000Sub001Block156Part007
    + surrogateDiagTailX0RatChunk000Sub001Block156Part008
    + surrogateDiagTailX0RatChunk000Sub001Block156Part009

def surrogateDiagonalTailChunk000Sub001Block156MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block156Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block156Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block156Part010
    + surrogateDiagTailX0RatChunk000Sub001Block156Part011
    + surrogateDiagTailX0RatChunk000Sub001Block156Part012
    + surrogateDiagTailX0RatChunk000Sub001Block156Part013
    + surrogateDiagTailX0RatChunk000Sub001Block156Part014
    + surrogateDiagTailX0RatChunk000Sub001Block156Part015
    + surrogateDiagTailX0RatChunk000Sub001Block156Part016
    + surrogateDiagTailX0RatChunk000Sub001Block156Part017
    + surrogateDiagTailX0RatChunk000Sub001Block156Part018
    + surrogateDiagTailX0RatChunk000Sub001Block156Part019

def surrogateDiagonalTailChunk000Sub001Block156TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block156Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block156Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block156Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block156Part020
    + surrogateDiagTailX0RatChunk000Sub001Block156Part021
    + surrogateDiagTailX0RatChunk000Sub001Block156Part022
    + surrogateDiagTailX0RatChunk000Sub001Block156Part023
    + surrogateDiagTailX0RatChunk000Sub001Block156Part024

def surrogateDiagonalTailChunk000Sub001Block156Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block156HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block156MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block156TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block156 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block156Part000
    + surrogateDiagTailX0RatChunk000Sub001Block156Part001
    + surrogateDiagTailX0RatChunk000Sub001Block156Part002
    + surrogateDiagTailX0RatChunk000Sub001Block156Part003
    + surrogateDiagTailX0RatChunk000Sub001Block156Part004
    + surrogateDiagTailX0RatChunk000Sub001Block156Part005
    + surrogateDiagTailX0RatChunk000Sub001Block156Part006
    + surrogateDiagTailX0RatChunk000Sub001Block156Part007
    + surrogateDiagTailX0RatChunk000Sub001Block156Part008
    + surrogateDiagTailX0RatChunk000Sub001Block156Part009
    + surrogateDiagTailX0RatChunk000Sub001Block156Part010
    + surrogateDiagTailX0RatChunk000Sub001Block156Part011
    + surrogateDiagTailX0RatChunk000Sub001Block156Part012
    + surrogateDiagTailX0RatChunk000Sub001Block156Part013
    + surrogateDiagTailX0RatChunk000Sub001Block156Part014
    + surrogateDiagTailX0RatChunk000Sub001Block156Part015
    + surrogateDiagTailX0RatChunk000Sub001Block156Part016
    + surrogateDiagTailX0RatChunk000Sub001Block156Part017
    + surrogateDiagTailX0RatChunk000Sub001Block156Part018
    + surrogateDiagTailX0RatChunk000Sub001Block156Part019
    + surrogateDiagTailX0RatChunk000Sub001Block156Part020
    + surrogateDiagTailX0RatChunk000Sub001Block156Part021
    + surrogateDiagTailX0RatChunk000Sub001Block156Part022
    + surrogateDiagTailX0RatChunk000Sub001Block156Part023
    + surrogateDiagTailX0RatChunk000Sub001Block156Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block156_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block156Head + surrogateDiagTailX0RatChunk000Sub001Block156Mid + surrogateDiagTailX0RatChunk000Sub001Block156Tail =
      surrogateDiagTailX0RatChunk000Sub001Block156 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block156Head surrogateDiagTailX0RatChunk000Sub001Block156Mid surrogateDiagTailX0RatChunk000Sub001Block156Tail surrogateDiagTailX0RatChunk000Sub001Block156
  ring

def SurrogateDiagonalTailChunk000Sub001Block156HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block156HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block156Head

def SurrogateDiagonalTailChunk000Sub001Block156MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block156MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block156Mid

def SurrogateDiagonalTailChunk000Sub001Block156TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block156TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block156Tail

theorem surrogateDiagonalTailChunk000Sub001Block156_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block156HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block156MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block156TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block156Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block156 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block156HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block156MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block156TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block156Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block156_eq_head_add_mid_add_tail

/-- Block 157 covers tail-support indices [8925,8950) and q from 14731 to 14774. -/

def TailChunk000Sub001Block157Part000SupportExplicit : Finset ℕ :=
  ([14731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part000 : ℚ :=
  (5425059025 : ℚ) / 47086654782276882

def SurrogateDiagonalTailChunk000Sub001Block157Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14731
    = surrogateDiagTailX0RatChunk000Sub001Block157Part000

theorem surrogateDiagonalTailChunk000Sub001Block157Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part000] using hcert

def TailChunk000Sub001Block157Part001SupportExplicit : Finset ℕ :=
  ([14734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part001 : ℚ :=
  (3276872641525 : ℚ) / 6630657249378060288

def SurrogateDiagonalTailChunk000Sub001Block157Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14734
    = surrogateDiagTailX0RatChunk000Sub001Block157Part001

theorem surrogateDiagonalTailChunk000Sub001Block157Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part001] using hcert

def TailChunk000Sub001Block157Part002SupportExplicit : Finset ℕ :=
  ([14735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part002 : ℚ :=
  (140612500961 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk000Sub001Block157Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14735
    = surrogateDiagTailX0RatChunk000Sub001Block157Part002

theorem surrogateDiagonalTailChunk000Sub001Block157Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part002] using hcert

def TailChunk000Sub001Block157Part003SupportExplicit : Finset ℕ :=
  ([14737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part003 : ℚ :=
  (3393424515625 : ℚ) / 29477138294366871552

def SurrogateDiagonalTailChunk000Sub001Block157Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14737
    = surrogateDiagTailX0RatChunk000Sub001Block157Part003

theorem surrogateDiagonalTailChunk000Sub001Block157Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part003] using hcert

def TailChunk000Sub001Block157Part004SupportExplicit : Finset ℕ :=
  ([14738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part004 : ℚ :=
  (848471265625 : ℚ) / 1842321143397929472

def SurrogateDiagonalTailChunk000Sub001Block157Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14738
    = surrogateDiagTailX0RatChunk000Sub001Block157Part004

theorem surrogateDiagonalTailChunk000Sub001Block157Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part004] using hcert

def TailChunk000Sub001Block157Part005SupportExplicit : Finset ℕ :=
  ([14741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part005 : ℚ :=
  (5432427025 : ℚ) / 47214651051761952

def SurrogateDiagonalTailChunk000Sub001Block157Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14741
    = surrogateDiagTailX0RatChunk000Sub001Block157Part005

theorem surrogateDiagonalTailChunk000Sub001Block157Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part005] using hcert

def TailChunk000Sub001Block157Part006SupportExplicit : Finset ℕ :=
  ([14743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part006 : ℚ :=
  (15214576251 : ℚ) / 119119683151462400

def SurrogateDiagonalTailChunk000Sub001Block157Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14743
    = surrogateDiagTailX0RatChunk000Sub001Block157Part006

theorem surrogateDiagonalTailChunk000Sub001Block157Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part006] using hcert

def TailChunk000Sub001Block157Part007SupportExplicit : Finset ℕ :=
  ([14745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part007 : ℚ :=
  (4281559193575 : ℚ) / 9524293233985486848

def SurrogateDiagonalTailChunk000Sub001Block157Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14745
    = surrogateDiagTailX0RatChunk000Sub001Block157Part007

theorem surrogateDiagonalTailChunk000Sub001Block157Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part007] using hcert

def TailChunk000Sub001Block157Part008SupportExplicit : Finset ℕ :=
  ([14746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part008 : ℚ :=
  (65864543153 : ℚ) / 134396153856000000

def SurrogateDiagonalTailChunk000Sub001Block157Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14746
    = surrogateDiagTailX0RatChunk000Sub001Block157Part008

theorem surrogateDiagonalTailChunk000Sub001Block157Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part008] using hcert

def TailChunk000Sub001Block157Part009SupportExplicit : Finset ℕ :=
  ([14747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part009 : ℚ :=
  (3398031390625 : ℚ) / 29557233726238719282

def SurrogateDiagonalTailChunk000Sub001Block157Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14747
    = surrogateDiagTailX0RatChunk000Sub001Block157Part009

theorem surrogateDiagonalTailChunk000Sub001Block157Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part009] using hcert

def TailChunk000Sub001Block157Part010SupportExplicit : Finset ℕ :=
  ([14753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part010 : ℚ :=
  (3400797015625 : ℚ) / 29605369266889162752

def SurrogateDiagonalTailChunk000Sub001Block157Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14753
    = surrogateDiagTailX0RatChunk000Sub001Block157Part010

theorem surrogateDiagonalTailChunk000Sub001Block157Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part010] using hcert

def TailChunk000Sub001Block157Part011SupportExplicit : Finset ℕ :=
  ([14754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part011 : ℚ :=
  (236122276775 : ℚ) / 182551064070711696

def SurrogateDiagonalTailChunk000Sub001Block157Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14754
    = surrogateDiagTailX0RatChunk000Sub001Block157Part011

theorem surrogateDiagonalTailChunk000Sub001Block157Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part011] using hcert

def TailChunk000Sub001Block157Part012SupportExplicit : Finset ℕ :=
  ([14755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part012 : ℚ :=
  (8037505649875 : ℚ) / 34627852981366161408

def SurrogateDiagonalTailChunk000Sub001Block157Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14755
    = surrogateDiagTailX0RatChunk000Sub001Block157Part012

theorem surrogateDiagonalTailChunk000Sub001Block157Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part012] using hcert

def TailChunk000Sub001Block157Part013SupportExplicit : Finset ℕ :=
  ([14757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part013 : ℚ :=
  (6047305508125 : ℚ) / 23404584695029857408

def SurrogateDiagonalTailChunk000Sub001Block157Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14757
    = surrogateDiagTailX0RatChunk000Sub001Block157Part013

theorem surrogateDiagonalTailChunk000Sub001Block157Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part013] using hcert

def TailChunk000Sub001Block157Part014SupportExplicit : Finset ℕ :=
  ([14758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part014 : ℚ :=
  (410045344625 : ℚ) / 828832156172257536

def SurrogateDiagonalTailChunk000Sub001Block157Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14758
    = surrogateDiagTailX0RatChunk000Sub001Block157Part014

theorem surrogateDiagonalTailChunk000Sub001Block157Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part014] using hcert

def TailChunk000Sub001Block157Part015SupportExplicit : Finset ℕ :=
  ([14759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part015 : ℚ :=
  (3403563765625 : ℚ) / 29653563577098867762

def SurrogateDiagonalTailChunk000Sub001Block157Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14759
    = surrogateDiagTailX0RatChunk000Sub001Block157Part015

theorem surrogateDiagonalTailChunk000Sub001Block157Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part015] using hcert

def TailChunk000Sub001Block157Part016SupportExplicit : Finset ℕ :=
  ([14761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part016 : ℚ :=
  (2133394132875 : ℚ) / 17059354064148021248

def SurrogateDiagonalTailChunk000Sub001Block157Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14761
    = surrogateDiagTailX0RatChunk000Sub001Block157Part016

theorem surrogateDiagonalTailChunk000Sub001Block157Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part016] using hcert

def TailChunk000Sub001Block157Part017SupportExplicit : Finset ℕ :=
  ([14763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part017 : ℚ :=
  (232879017925 : ℚ) / 507901343298748416

def SurrogateDiagonalTailChunk000Sub001Block157Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14763
    = surrogateDiagTailX0RatChunk000Sub001Block157Part017

theorem surrogateDiagonalTailChunk000Sub001Block157Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part017] using hcert

def TailChunk000Sub001Block157Part018SupportExplicit : Finset ℕ :=
  ([14765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part018 : ℚ :=
  (9261069839275 : ℚ) / 48610740494884405248

def SurrogateDiagonalTailChunk000Sub001Block157Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14765
    = surrogateDiagTailX0RatChunk000Sub001Block157Part018

theorem surrogateDiagonalTailChunk000Sub001Block157Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part018] using hcert

def TailChunk000Sub001Block157Part019SupportExplicit : Finset ℕ :=
  ([14766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part019 : ℚ :=
  (1776471548275 : ℚ) / 1183207805209233408

def SurrogateDiagonalTailChunk000Sub001Block157Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14766
    = surrogateDiagTailX0RatChunk000Sub001Block157Part019

theorem surrogateDiagonalTailChunk000Sub001Block157Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part019] using hcert

def TailChunk000Sub001Block157Part020SupportExplicit : Finset ℕ :=
  ([14767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part020 : ℚ :=
  (3407254515625 : ℚ) / 29717914159340207442

def SurrogateDiagonalTailChunk000Sub001Block157Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14767
    = surrogateDiagTailX0RatChunk000Sub001Block157Part020

theorem surrogateDiagonalTailChunk000Sub001Block157Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part020] using hcert

def TailChunk000Sub001Block157Part021SupportExplicit : Finset ℕ :=
  ([14770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part021 : ℚ :=
  (40341505163 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub001Block157Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14770
    = surrogateDiagTailX0RatChunk000Sub001Block157Part021

theorem surrogateDiagonalTailChunk000Sub001Block157Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part021] using hcert

def TailChunk000Sub001Block157Part022SupportExplicit : Finset ℕ :=
  ([14771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part022 : ℚ :=
  (5454561025 : ℚ) / 47600205915965682

def SurrogateDiagonalTailChunk000Sub001Block157Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14771
    = surrogateDiagTailX0RatChunk000Sub001Block157Part022

theorem surrogateDiagonalTailChunk000Sub001Block157Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part022] using hcert

def TailChunk000Sub001Block157Part023SupportExplicit : Finset ℕ :=
  ([14773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part023 : ℚ :=
  (22859645513 : ℚ) / 134794659653222400

def SurrogateDiagonalTailChunk000Sub001Block157Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14773
    = surrogateDiagTailX0RatChunk000Sub001Block157Part023

theorem surrogateDiagonalTailChunk000Sub001Block157Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part023] using hcert

def TailChunk000Sub001Block157Part024SupportExplicit : Finset ℕ :=
  ([14774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block157Part024 : ℚ :=
  (826803308425 : ℚ) / 1694934679320993792

def SurrogateDiagonalTailChunk000Sub001Block157Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14774
    = surrogateDiagTailX0RatChunk000Sub001Block157Part024

theorem surrogateDiagonalTailChunk000Sub001Block157Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block157Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block157Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block157Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block157Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block157Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block157Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block157HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block157Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block157Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block157Part000
    + surrogateDiagTailX0RatChunk000Sub001Block157Part001
    + surrogateDiagTailX0RatChunk000Sub001Block157Part002
    + surrogateDiagTailX0RatChunk000Sub001Block157Part003
    + surrogateDiagTailX0RatChunk000Sub001Block157Part004
    + surrogateDiagTailX0RatChunk000Sub001Block157Part005
    + surrogateDiagTailX0RatChunk000Sub001Block157Part006
    + surrogateDiagTailX0RatChunk000Sub001Block157Part007
    + surrogateDiagTailX0RatChunk000Sub001Block157Part008
    + surrogateDiagTailX0RatChunk000Sub001Block157Part009

def surrogateDiagonalTailChunk000Sub001Block157MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block157Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block157Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block157Part010
    + surrogateDiagTailX0RatChunk000Sub001Block157Part011
    + surrogateDiagTailX0RatChunk000Sub001Block157Part012
    + surrogateDiagTailX0RatChunk000Sub001Block157Part013
    + surrogateDiagTailX0RatChunk000Sub001Block157Part014
    + surrogateDiagTailX0RatChunk000Sub001Block157Part015
    + surrogateDiagTailX0RatChunk000Sub001Block157Part016
    + surrogateDiagTailX0RatChunk000Sub001Block157Part017
    + surrogateDiagTailX0RatChunk000Sub001Block157Part018
    + surrogateDiagTailX0RatChunk000Sub001Block157Part019

def surrogateDiagonalTailChunk000Sub001Block157TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block157Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block157Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block157Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block157Part020
    + surrogateDiagTailX0RatChunk000Sub001Block157Part021
    + surrogateDiagTailX0RatChunk000Sub001Block157Part022
    + surrogateDiagTailX0RatChunk000Sub001Block157Part023
    + surrogateDiagTailX0RatChunk000Sub001Block157Part024

def surrogateDiagonalTailChunk000Sub001Block157Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block157HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block157MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block157TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block157 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block157Part000
    + surrogateDiagTailX0RatChunk000Sub001Block157Part001
    + surrogateDiagTailX0RatChunk000Sub001Block157Part002
    + surrogateDiagTailX0RatChunk000Sub001Block157Part003
    + surrogateDiagTailX0RatChunk000Sub001Block157Part004
    + surrogateDiagTailX0RatChunk000Sub001Block157Part005
    + surrogateDiagTailX0RatChunk000Sub001Block157Part006
    + surrogateDiagTailX0RatChunk000Sub001Block157Part007
    + surrogateDiagTailX0RatChunk000Sub001Block157Part008
    + surrogateDiagTailX0RatChunk000Sub001Block157Part009
    + surrogateDiagTailX0RatChunk000Sub001Block157Part010
    + surrogateDiagTailX0RatChunk000Sub001Block157Part011
    + surrogateDiagTailX0RatChunk000Sub001Block157Part012
    + surrogateDiagTailX0RatChunk000Sub001Block157Part013
    + surrogateDiagTailX0RatChunk000Sub001Block157Part014
    + surrogateDiagTailX0RatChunk000Sub001Block157Part015
    + surrogateDiagTailX0RatChunk000Sub001Block157Part016
    + surrogateDiagTailX0RatChunk000Sub001Block157Part017
    + surrogateDiagTailX0RatChunk000Sub001Block157Part018
    + surrogateDiagTailX0RatChunk000Sub001Block157Part019
    + surrogateDiagTailX0RatChunk000Sub001Block157Part020
    + surrogateDiagTailX0RatChunk000Sub001Block157Part021
    + surrogateDiagTailX0RatChunk000Sub001Block157Part022
    + surrogateDiagTailX0RatChunk000Sub001Block157Part023
    + surrogateDiagTailX0RatChunk000Sub001Block157Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block157_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block157Head + surrogateDiagTailX0RatChunk000Sub001Block157Mid + surrogateDiagTailX0RatChunk000Sub001Block157Tail =
      surrogateDiagTailX0RatChunk000Sub001Block157 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block157Head surrogateDiagTailX0RatChunk000Sub001Block157Mid surrogateDiagTailX0RatChunk000Sub001Block157Tail surrogateDiagTailX0RatChunk000Sub001Block157
  ring

def SurrogateDiagonalTailChunk000Sub001Block157HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block157HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block157Head

def SurrogateDiagonalTailChunk000Sub001Block157MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block157MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block157Mid

def SurrogateDiagonalTailChunk000Sub001Block157TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block157TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block157Tail

theorem surrogateDiagonalTailChunk000Sub001Block157_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block157HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block157MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block157TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block157Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block157 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block157HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block157MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block157TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block157Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block157_eq_head_add_mid_add_tail

/-- Block 158 covers tail-support indices [8950,8975) and q from 14777 to 14817. -/

def TailChunk000Sub001Block158Part000SupportExplicit : Finset ℕ :=
  ([14777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part000 : ℚ :=
  (26442081967 : ℚ) / 160583785055944200

def SurrogateDiagonalTailChunk000Sub001Block158Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14777
    = surrogateDiagTailX0RatChunk000Sub001Block158Part000

theorem surrogateDiagonalTailChunk000Sub001Block158Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part000] using hcert

def TailChunk000Sub001Block158Part001SupportExplicit : Finset ℕ :=
  ([14779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part001 : ℚ :=
  (3412794390625 : ℚ) / 29814636338691164082

def SurrogateDiagonalTailChunk000Sub001Block158Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14779
    = surrogateDiagTailX0RatChunk000Sub001Block158Part001

theorem surrogateDiagonalTailChunk000Sub001Block158Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part001] using hcert

def TailChunk000Sub001Block158Part002SupportExplicit : Finset ℕ :=
  ([14781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part002 : ℚ :=
  (1341411627775 : ℚ) / 4234274740487135232

def SurrogateDiagonalTailChunk000Sub001Block158Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14781
    = surrogateDiagTailX0RatChunk000Sub001Block158Part002

theorem surrogateDiagonalTailChunk000Sub001Block158Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part002] using hcert

def TailChunk000Sub001Block158Part003SupportExplicit : Finset ℕ :=
  ([14782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part003 : ℚ :=
  (3167589951925 : ℚ) / 5948997435018528768

def SurrogateDiagonalTailChunk000Sub001Block158Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14782
    = surrogateDiagTailX0RatChunk000Sub001Block158Part003

theorem surrogateDiagonalTailChunk000Sub001Block158Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part003] using hcert

def TailChunk000Sub001Block158Part004SupportExplicit : Finset ℕ :=
  ([14783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part004 : ℚ :=
  (3414642015625 : ℚ) / 29846929470137186322

def SurrogateDiagonalTailChunk000Sub001Block158Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14783
    = surrogateDiagTailX0RatChunk000Sub001Block158Part004

theorem surrogateDiagonalTailChunk000Sub001Block158Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part004] using hcert

def TailChunk000Sub001Block158Part005SupportExplicit : Finset ℕ :=
  ([14785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part005 : ℚ :=
  (546199140625 : ℚ) / 3054671833808160768

def SurrogateDiagonalTailChunk000Sub001Block158Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14785
    = surrogateDiagTailX0RatChunk000Sub001Block158Part005

theorem surrogateDiagonalTailChunk000Sub001Block158Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part005] using hcert

def TailChunk000Sub001Block158Part006SupportExplicit : Finset ℕ :=
  ([14786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part006 : ℚ :=
  (854007015625 : ℚ) / 1866442866861146112

def SurrogateDiagonalTailChunk000Sub001Block158Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14786
    = surrogateDiagTailX0RatChunk000Sub001Block158Part006

theorem surrogateDiagonalTailChunk000Sub001Block158Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part006] using hcert

def TailChunk000Sub001Block158Part007SupportExplicit : Finset ℕ :=
  ([14789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part007 : ℚ :=
  (6328240548875 : ℚ) / 49753965282502561344

def SurrogateDiagonalTailChunk000Sub001Block158Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14789
    = surrogateDiagTailX0RatChunk000Sub001Block158Part007

theorem surrogateDiagonalTailChunk000Sub001Block158Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part007] using hcert

def TailChunk000Sub001Block158Part008SupportExplicit : Finset ℕ :=
  ([14790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part008 : ℚ :=
  (426488123625 : ℚ) / 137523718946553856

def SurrogateDiagonalTailChunk000Sub001Block158Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14790
    = surrogateDiagTailX0RatChunk000Sub001Block158Part008

theorem surrogateDiagonalTailChunk000Sub001Block158Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part008] using hcert

def TailChunk000Sub001Block158Part009SupportExplicit : Finset ℕ :=
  ([14791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part009 : ℚ :=
  (10317547468225 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk000Sub001Block158Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14791
    = surrogateDiagTailX0RatChunk000Sub001Block158Part009

theorem surrogateDiagonalTailChunk000Sub001Block158Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part009] using hcert

def TailChunk000Sub001Block158Part010SupportExplicit : Finset ℕ :=
  ([14793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part010 : ℚ :=
  (243073980277 : ℚ) / 945354095428483200

def SurrogateDiagonalTailChunk000Sub001Block158Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14793
    = surrogateDiagTailX0RatChunk000Sub001Block158Part010

theorem surrogateDiagonalTailChunk000Sub001Block158Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part010] using hcert

def TailChunk000Sub001Block158Part011SupportExplicit : Finset ℕ :=
  ([14794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part011 : ℚ :=
  (5994572675 : ℚ) / 10540840090788864

def SurrogateDiagonalTailChunk000Sub001Block158Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14794
    = surrogateDiagTailX0RatChunk000Sub001Block158Part011

theorem surrogateDiagonalTailChunk000Sub001Block158Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part011] using hcert

def TailChunk000Sub001Block158Part012SupportExplicit : Finset ℕ :=
  ([14795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part012 : ℚ :=
  (316907097889 : ℚ) / 1320887990629171200

def SurrogateDiagonalTailChunk000Sub001Block158Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14795
    = surrogateDiagTailX0RatChunk000Sub001Block158Part012

theorem surrogateDiagonalTailChunk000Sub001Block158Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part012] using hcert

def TailChunk000Sub001Block158Part013SupportExplicit : Finset ℕ :=
  ([14797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part013 : ℚ :=
  (3421112640625 : ℚ) / 29960162054276166432

def SurrogateDiagonalTailChunk000Sub001Block158Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14797
    = surrogateDiagTailX0RatChunk000Sub001Block158Part013

theorem surrogateDiagonalTailChunk000Sub001Block158Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part013] using hcert

def TailChunk000Sub001Block158Part014SupportExplicit : Finset ℕ :=
  ([14799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part014 : ℚ :=
  (6081780506725 : ℚ) / 23672226808316971008

def SurrogateDiagonalTailChunk000Sub001Block158Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14799
    = surrogateDiagTailX0RatChunk000Sub001Block158Part014

theorem surrogateDiagonalTailChunk000Sub001Block158Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part014] using hcert

def TailChunk000Sub001Block158Part015SupportExplicit : Finset ℕ :=
  ([14802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part015 : ℚ :=
  (118830636475 : ℚ) / 92469635969988168

def SurrogateDiagonalTailChunk000Sub001Block158Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14802
    = surrogateDiagTailX0RatChunk000Sub001Block158Part015

theorem surrogateDiagonalTailChunk000Sub001Block158Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part015] using hcert

def TailChunk000Sub001Block158Part016SupportExplicit : Finset ℕ :=
  ([14803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part016 : ℚ :=
  (177666177279 : ℚ) / 1498342489941606400

def SurrogateDiagonalTailChunk000Sub001Block158Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14803
    = surrogateDiagTailX0RatChunk000Sub001Block158Part016

theorem surrogateDiagonalTailChunk000Sub001Block158Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part016] using hcert

def TailChunk000Sub001Block158Part017SupportExplicit : Finset ℕ :=
  ([14806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part017 : ℚ :=
  (120945722101 : ℚ) / 203968894677811200

def SurrogateDiagonalTailChunk000Sub001Block158Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14806
    = surrogateDiagTailX0RatChunk000Sub001Block158Part017

theorem surrogateDiagonalTailChunk000Sub001Block158Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part017] using hcert

def TailChunk000Sub001Block158Part018SupportExplicit : Finset ℕ :=
  ([14807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part018 : ℚ :=
  (10549175218375 : ℚ) / 64477399895431446528

def SurrogateDiagonalTailChunk000Sub001Block158Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14807
    = surrogateDiagTailX0RatChunk000Sub001Block158Part018

theorem surrogateDiagonalTailChunk000Sub001Block158Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part018] using hcert

def TailChunk000Sub001Block158Part019SupportExplicit : Finset ℕ :=
  ([14809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part019 : ℚ :=
  (176403918633 : ℚ) / 1473796783750000000

def SurrogateDiagonalTailChunk000Sub001Block158Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14809
    = surrogateDiagTailX0RatChunk000Sub001Block158Part019

theorem surrogateDiagonalTailChunk000Sub001Block158Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part019] using hcert

def TailChunk000Sub001Block158Part020SupportExplicit : Finset ℕ :=
  ([14810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part020 : ℚ :=
  (32877781239 : ℚ) / 40949860099686400

def SurrogateDiagonalTailChunk000Sub001Block158Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14810
    = surrogateDiagTailX0RatChunk000Sub001Block158Part020

theorem surrogateDiagonalTailChunk000Sub001Block158Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part020] using hcert

def TailChunk000Sub001Block158Part021SupportExplicit : Finset ℕ :=
  ([14811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part021 : ℚ :=
  (6091648506325 : ℚ) / 23749115829279817728

def SurrogateDiagonalTailChunk000Sub001Block158Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14811
    = surrogateDiagTailX0RatChunk000Sub001Block158Part021

theorem surrogateDiagonalTailChunk000Sub001Block158Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part021] using hcert

def TailChunk000Sub001Block158Part022SupportExplicit : Finset ℕ :=
  ([14813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part022 : ℚ :=
  (3428515140625 : ℚ) / 30089964895170069792

def SurrogateDiagonalTailChunk000Sub001Block158Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14813
    = surrogateDiagTailX0RatChunk000Sub001Block158Part022

theorem surrogateDiagonalTailChunk000Sub001Block158Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part022] using hcert

def TailChunk000Sub001Block158Part023SupportExplicit : Finset ℕ :=
  ([14815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part023 : ℚ :=
  (9323912004025 : ℚ) / 49272777142438545408

def SurrogateDiagonalTailChunk000Sub001Block158Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14815
    = surrogateDiagTailX0RatChunk000Sub001Block158Part023

theorem surrogateDiagonalTailChunk000Sub001Block158Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part023] using hcert

def TailChunk000Sub001Block158Part024SupportExplicit : Finset ℕ :=
  ([14817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block158Part024 : ℚ :=
  (208965451207 : ℚ) / 644642432561971200

def SurrogateDiagonalTailChunk000Sub001Block158Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14817
    = surrogateDiagTailX0RatChunk000Sub001Block158Part024

theorem surrogateDiagonalTailChunk000Sub001Block158Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block158Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block158Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block158Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block158Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block158Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block158Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block158HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block158Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block158Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block158Part000
    + surrogateDiagTailX0RatChunk000Sub001Block158Part001
    + surrogateDiagTailX0RatChunk000Sub001Block158Part002
    + surrogateDiagTailX0RatChunk000Sub001Block158Part003
    + surrogateDiagTailX0RatChunk000Sub001Block158Part004
    + surrogateDiagTailX0RatChunk000Sub001Block158Part005
    + surrogateDiagTailX0RatChunk000Sub001Block158Part006
    + surrogateDiagTailX0RatChunk000Sub001Block158Part007
    + surrogateDiagTailX0RatChunk000Sub001Block158Part008
    + surrogateDiagTailX0RatChunk000Sub001Block158Part009

def surrogateDiagonalTailChunk000Sub001Block158MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block158Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block158Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block158Part010
    + surrogateDiagTailX0RatChunk000Sub001Block158Part011
    + surrogateDiagTailX0RatChunk000Sub001Block158Part012
    + surrogateDiagTailX0RatChunk000Sub001Block158Part013
    + surrogateDiagTailX0RatChunk000Sub001Block158Part014
    + surrogateDiagTailX0RatChunk000Sub001Block158Part015
    + surrogateDiagTailX0RatChunk000Sub001Block158Part016
    + surrogateDiagTailX0RatChunk000Sub001Block158Part017
    + surrogateDiagTailX0RatChunk000Sub001Block158Part018
    + surrogateDiagTailX0RatChunk000Sub001Block158Part019

def surrogateDiagonalTailChunk000Sub001Block158TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block158Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block158Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block158Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block158Part020
    + surrogateDiagTailX0RatChunk000Sub001Block158Part021
    + surrogateDiagTailX0RatChunk000Sub001Block158Part022
    + surrogateDiagTailX0RatChunk000Sub001Block158Part023
    + surrogateDiagTailX0RatChunk000Sub001Block158Part024

def surrogateDiagonalTailChunk000Sub001Block158Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block158HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block158MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block158TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block158 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block158Part000
    + surrogateDiagTailX0RatChunk000Sub001Block158Part001
    + surrogateDiagTailX0RatChunk000Sub001Block158Part002
    + surrogateDiagTailX0RatChunk000Sub001Block158Part003
    + surrogateDiagTailX0RatChunk000Sub001Block158Part004
    + surrogateDiagTailX0RatChunk000Sub001Block158Part005
    + surrogateDiagTailX0RatChunk000Sub001Block158Part006
    + surrogateDiagTailX0RatChunk000Sub001Block158Part007
    + surrogateDiagTailX0RatChunk000Sub001Block158Part008
    + surrogateDiagTailX0RatChunk000Sub001Block158Part009
    + surrogateDiagTailX0RatChunk000Sub001Block158Part010
    + surrogateDiagTailX0RatChunk000Sub001Block158Part011
    + surrogateDiagTailX0RatChunk000Sub001Block158Part012
    + surrogateDiagTailX0RatChunk000Sub001Block158Part013
    + surrogateDiagTailX0RatChunk000Sub001Block158Part014
    + surrogateDiagTailX0RatChunk000Sub001Block158Part015
    + surrogateDiagTailX0RatChunk000Sub001Block158Part016
    + surrogateDiagTailX0RatChunk000Sub001Block158Part017
    + surrogateDiagTailX0RatChunk000Sub001Block158Part018
    + surrogateDiagTailX0RatChunk000Sub001Block158Part019
    + surrogateDiagTailX0RatChunk000Sub001Block158Part020
    + surrogateDiagTailX0RatChunk000Sub001Block158Part021
    + surrogateDiagTailX0RatChunk000Sub001Block158Part022
    + surrogateDiagTailX0RatChunk000Sub001Block158Part023
    + surrogateDiagTailX0RatChunk000Sub001Block158Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block158_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block158Head + surrogateDiagTailX0RatChunk000Sub001Block158Mid + surrogateDiagTailX0RatChunk000Sub001Block158Tail =
      surrogateDiagTailX0RatChunk000Sub001Block158 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block158Head surrogateDiagTailX0RatChunk000Sub001Block158Mid surrogateDiagTailX0RatChunk000Sub001Block158Tail surrogateDiagTailX0RatChunk000Sub001Block158
  ring

def SurrogateDiagonalTailChunk000Sub001Block158HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block158HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block158Head

def SurrogateDiagonalTailChunk000Sub001Block158MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block158MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block158Mid

def SurrogateDiagonalTailChunk000Sub001Block158TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block158TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block158Tail

theorem surrogateDiagonalTailChunk000Sub001Block158_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block158HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block158MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block158TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block158Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block158 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block158HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block158MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block158TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block158Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block158_eq_head_add_mid_add_tail

/-- Block 159 covers tail-support indices [8975,9000) and q from 14818 to 14857. -/

def TailChunk000Sub001Block159Part000SupportExplicit : Finset ℕ :=
  ([14818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part000 : ℚ :=
  (32633565667 : ℚ) / 64985985002080800

def SurrogateDiagonalTailChunk000Sub001Block159Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14818
    = surrogateDiagTailX0RatChunk000Sub001Block159Part000

theorem surrogateDiagonalTailChunk000Sub001Block159Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part000] using hcert

def TailChunk000Sub001Block159Part001SupportExplicit : Finset ℕ :=
  ([14819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part001 : ℚ :=
  (9572120885875 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk000Sub001Block159Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14819
    = surrogateDiagTailX0RatChunk000Sub001Block159Part001

theorem surrogateDiagonalTailChunk000Sub001Block159Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part001] using hcert

def TailChunk000Sub001Block159Part002SupportExplicit : Finset ℕ :=
  ([14821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part002 : ℚ :=
  (5491551025 : ℚ) / 48248038807985952

def SurrogateDiagonalTailChunk000Sub001Block159Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14821
    = surrogateDiagTailX0RatChunk000Sub001Block159Part002

theorem surrogateDiagonalTailChunk000Sub001Block159Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part002] using hcert

def TailChunk000Sub001Block159Part003SupportExplicit : Finset ℕ :=
  ([14822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part003 : ℚ :=
  (1373073025 : ℚ) / 3015502425499122

def SurrogateDiagonalTailChunk000Sub001Block159Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14822
    = surrogateDiagTailX0RatChunk000Sub001Block159Part003

theorem surrogateDiagonalTailChunk000Sub001Block159Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part003] using hcert

def TailChunk000Sub001Block159Part004SupportExplicit : Finset ℕ :=
  ([14826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part004 : ℚ :=
  (86692566775 : ℚ) / 44223182369980416

def SurrogateDiagonalTailChunk000Sub001Block159Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14826
    = surrogateDiagTailX0RatChunk000Sub001Block159Part004

theorem surrogateDiagonalTailChunk000Sub001Block159Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part004] using hcert

def TailChunk000Sub001Block159Part005SupportExplicit : Finset ℕ :=
  ([14827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part005 : ℚ :=
  (3434998890625 : ℚ) / 30203887966677009522

def SurrogateDiagonalTailChunk000Sub001Block159Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14827
    = surrogateDiagTailX0RatChunk000Sub001Block159Part005

theorem surrogateDiagonalTailChunk000Sub001Block159Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part005] using hcert

def TailChunk000Sub001Block159Part006SupportExplicit : Finset ℕ :=
  ([14829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part006 : ℚ :=
  (6106465505725 : ℚ) / 23864800368732451968

def SurrogateDiagonalTailChunk000Sub001Block159Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14829
    = surrogateDiagTailX0RatChunk000Sub001Block159Part006

theorem surrogateDiagonalTailChunk000Sub001Block159Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part006] using hcert

def TailChunk000Sub001Block159Part007SupportExplicit : Finset ℕ :=
  ([14830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part007 : ℚ :=
  (2472499129825 : ℚ) / 3087874483711100928

def SurrogateDiagonalTailChunk000Sub001Block159Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14830
    = surrogateDiagTailX0RatChunk000Sub001Block159Part007

theorem surrogateDiagonalTailChunk000Sub001Block159Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part007] using hcert

def TailChunk000Sub001Block159Part008SupportExplicit : Finset ℕ :=
  ([14831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part008 : ℚ :=
  (5498964025 : ℚ) / 48378394799421042

def SurrogateDiagonalTailChunk000Sub001Block159Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14831
    = surrogateDiagTailX0RatChunk000Sub001Block159Part008

theorem surrogateDiagonalTailChunk000Sub001Block159Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part008] using hcert

def TailChunk000Sub001Block159Part009SupportExplicit : Finset ℕ :=
  ([14833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part009 : ℚ :=
  (4608305093075 : ℚ) / 23141254954049224704

def SurrogateDiagonalTailChunk000Sub001Block159Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14833
    = surrogateDiagTailX0RatChunk000Sub001Block159Part009

theorem surrogateDiagonalTailChunk000Sub001Block159Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part009] using hcert

def TailChunk000Sub001Block159Part010SupportExplicit : Finset ℕ :=
  ([14834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part010 : ℚ :=
  (859560765625 : ℚ) / 1890800689938043392

def SurrogateDiagonalTailChunk000Sub001Block159Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14834
    = surrogateDiagTailX0RatChunk000Sub001Block159Part010

theorem surrogateDiagonalTailChunk000Sub001Block159Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part010] using hcert

def TailChunk000Sub001Block159Part011SupportExplicit : Finset ℕ :=
  ([14835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part011 : ℚ :=
  (72802450025 : ℚ) / 138255027174899712

def SurrogateDiagonalTailChunk000Sub001Block159Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14835
    = surrogateDiagTailX0RatChunk000Sub001Block159Part011

theorem surrogateDiagonalTailChunk000Sub001Block159Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part011] using hcert

def TailChunk000Sub001Block159Part012SupportExplicit : Finset ℕ :=
  ([14837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part012 : ℚ :=
  (58189406201 : ℚ) / 477852991488000000

def SurrogateDiagonalTailChunk000Sub001Block159Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14837
    = surrogateDiagTailX0RatChunk000Sub001Block159Part012

theorem surrogateDiagonalTailChunk000Sub001Block159Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part012] using hcert

def TailChunk000Sub001Block159Part013SupportExplicit : Finset ℕ :=
  ([14838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part013 : ℚ :=
  (955275207425 : ℚ) / 746982988617498624

def SurrogateDiagonalTailChunk000Sub001Block159Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14838
    = surrogateDiagTailX0RatChunk000Sub001Block159Part013

theorem surrogateDiagonalTailChunk000Sub001Block159Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part013] using hcert

def TailChunk000Sub001Block159Part014SupportExplicit : Finset ℕ :=
  ([14839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part014 : ℚ :=
  (417886933633 : ℚ) / 2520977854752000000

def SurrogateDiagonalTailChunk000Sub001Block159Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14839
    = surrogateDiagTailX0RatChunk000Sub001Block159Part014

theorem surrogateDiagonalTailChunk000Sub001Block159Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part014] using hcert

def TailChunk000Sub001Block159Part015SupportExplicit : Finset ℕ :=
  ([14842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part015 : ℚ :=
  (22051136779 : ℚ) / 44798717952000000

def SurrogateDiagonalTailChunk000Sub001Block159Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14842
    = surrogateDiagTailX0RatChunk000Sub001Block159Part015

theorem surrogateDiagonalTailChunk000Sub001Block159Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part015] using hcert

def TailChunk000Sub001Block159Part016SupportExplicit : Finset ℕ :=
  ([14843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part016 : ℚ :=
  (3442416390625 : ℚ) / 30334481535971370162

def SurrogateDiagonalTailChunk000Sub001Block159Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14843
    = surrogateDiagTailX0RatChunk000Sub001Block159Part016

theorem surrogateDiagonalTailChunk000Sub001Block159Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part016] using hcert

def TailChunk000Sub001Block159Part017SupportExplicit : Finset ℕ :=
  ([14845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part017 : ℚ :=
  (9361719312475 : ℚ) / 49673231112539209728

def SurrogateDiagonalTailChunk000Sub001Block159Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14845
    = surrogateDiagTailX0RatChunk000Sub001Block159Part017

theorem surrogateDiagonalTailChunk000Sub001Block159Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part017] using hcert

def TailChunk000Sub001Block159Part018SupportExplicit : Finset ℕ :=
  ([14846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part018 : ℚ :=
  (858568633 : ℚ) / 1520368156828800

def SurrogateDiagonalTailChunk000Sub001Block159Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14846
    = surrogateDiagTailX0RatChunk000Sub001Block159Part018

theorem surrogateDiagonalTailChunk000Sub001Block159Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part018] using hcert

def TailChunk000Sub001Block159Part019SupportExplicit : Finset ℕ :=
  ([14849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part019 : ℚ :=
  (104046245117 : ℚ) / 845889143747149440

def SurrogateDiagonalTailChunk000Sub001Block159Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14849
    = surrogateDiagTailX0RatChunk000Sub001Block159Part019

theorem surrogateDiagonalTailChunk000Sub001Block159Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part019] using hcert

def TailChunk000Sub001Block159Part020SupportExplicit : Finset ℕ :=
  ([14851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part020 : ℚ :=
  (220552201 : ℚ) / 1945595961634050

def SurrogateDiagonalTailChunk000Sub001Block159Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14851
    = surrogateDiagTailX0RatChunk000Sub001Block159Part020

theorem surrogateDiagonalTailChunk000Sub001Block159Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part020] using hcert

def TailChunk000Sub001Block159Part021SupportExplicit : Finset ℕ :=
  ([14853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part021 : ℚ :=
  (1225625051 : ℚ) / 19215762584040000

def SurrogateDiagonalTailChunk000Sub001Block159Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14853
    = surrogateDiagTailX0RatChunk000Sub001Block159Part021

theorem surrogateDiagonalTailChunk000Sub001Block159Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part021] using hcert

def TailChunk000Sub001Block159Part022SupportExplicit : Finset ℕ :=
  ([14854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part022 : ℚ :=
  (11304236653 : ℚ) / 163649737418803200

def SurrogateDiagonalTailChunk000Sub001Block159Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14854
    = surrogateDiagTailX0RatChunk000Sub001Block159Part022

theorem surrogateDiagonalTailChunk000Sub001Block159Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part022] using hcert

def TailChunk000Sub001Block159Part023SupportExplicit : Finset ℕ :=
  ([14855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part023 : ℚ :=
  (4420456529 : ℚ) / 398458052942653440

def SurrogateDiagonalTailChunk000Sub001Block159Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14855
    = surrogateDiagTailX0RatChunk000Sub001Block159Part023

theorem surrogateDiagonalTailChunk000Sub001Block159Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part023] using hcert

def TailChunk000Sub001Block159Part024SupportExplicit : Finset ℕ :=
  ([14857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block159Part024 : ℚ :=
  (20168470075 : ℚ) / 28372805853749612832

def SurrogateDiagonalTailChunk000Sub001Block159Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 14857
    = surrogateDiagTailX0RatChunk000Sub001Block159Part024

theorem surrogateDiagonalTailChunk000Sub001Block159Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block159Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block159Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block159Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block159Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block159Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block159Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block159HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block159Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block159Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block159Part000
    + surrogateDiagTailX0RatChunk000Sub001Block159Part001
    + surrogateDiagTailX0RatChunk000Sub001Block159Part002
    + surrogateDiagTailX0RatChunk000Sub001Block159Part003
    + surrogateDiagTailX0RatChunk000Sub001Block159Part004
    + surrogateDiagTailX0RatChunk000Sub001Block159Part005
    + surrogateDiagTailX0RatChunk000Sub001Block159Part006
    + surrogateDiagTailX0RatChunk000Sub001Block159Part007
    + surrogateDiagTailX0RatChunk000Sub001Block159Part008
    + surrogateDiagTailX0RatChunk000Sub001Block159Part009

def surrogateDiagonalTailChunk000Sub001Block159MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block159Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block159Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block159Part010
    + surrogateDiagTailX0RatChunk000Sub001Block159Part011
    + surrogateDiagTailX0RatChunk000Sub001Block159Part012
    + surrogateDiagTailX0RatChunk000Sub001Block159Part013
    + surrogateDiagTailX0RatChunk000Sub001Block159Part014
    + surrogateDiagTailX0RatChunk000Sub001Block159Part015
    + surrogateDiagTailX0RatChunk000Sub001Block159Part016
    + surrogateDiagTailX0RatChunk000Sub001Block159Part017
    + surrogateDiagTailX0RatChunk000Sub001Block159Part018
    + surrogateDiagTailX0RatChunk000Sub001Block159Part019

def surrogateDiagonalTailChunk000Sub001Block159TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block159Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block159Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block159Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block159Part020
    + surrogateDiagTailX0RatChunk000Sub001Block159Part021
    + surrogateDiagTailX0RatChunk000Sub001Block159Part022
    + surrogateDiagTailX0RatChunk000Sub001Block159Part023
    + surrogateDiagTailX0RatChunk000Sub001Block159Part024

def surrogateDiagonalTailChunk000Sub001Block159Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block159HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block159MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block159TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block159 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block159Part000
    + surrogateDiagTailX0RatChunk000Sub001Block159Part001
    + surrogateDiagTailX0RatChunk000Sub001Block159Part002
    + surrogateDiagTailX0RatChunk000Sub001Block159Part003
    + surrogateDiagTailX0RatChunk000Sub001Block159Part004
    + surrogateDiagTailX0RatChunk000Sub001Block159Part005
    + surrogateDiagTailX0RatChunk000Sub001Block159Part006
    + surrogateDiagTailX0RatChunk000Sub001Block159Part007
    + surrogateDiagTailX0RatChunk000Sub001Block159Part008
    + surrogateDiagTailX0RatChunk000Sub001Block159Part009
    + surrogateDiagTailX0RatChunk000Sub001Block159Part010
    + surrogateDiagTailX0RatChunk000Sub001Block159Part011
    + surrogateDiagTailX0RatChunk000Sub001Block159Part012
    + surrogateDiagTailX0RatChunk000Sub001Block159Part013
    + surrogateDiagTailX0RatChunk000Sub001Block159Part014
    + surrogateDiagTailX0RatChunk000Sub001Block159Part015
    + surrogateDiagTailX0RatChunk000Sub001Block159Part016
    + surrogateDiagTailX0RatChunk000Sub001Block159Part017
    + surrogateDiagTailX0RatChunk000Sub001Block159Part018
    + surrogateDiagTailX0RatChunk000Sub001Block159Part019
    + surrogateDiagTailX0RatChunk000Sub001Block159Part020
    + surrogateDiagTailX0RatChunk000Sub001Block159Part021
    + surrogateDiagTailX0RatChunk000Sub001Block159Part022
    + surrogateDiagTailX0RatChunk000Sub001Block159Part023
    + surrogateDiagTailX0RatChunk000Sub001Block159Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block159_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block159Head + surrogateDiagTailX0RatChunk000Sub001Block159Mid + surrogateDiagTailX0RatChunk000Sub001Block159Tail =
      surrogateDiagTailX0RatChunk000Sub001Block159 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block159Head surrogateDiagTailX0RatChunk000Sub001Block159Mid surrogateDiagTailX0RatChunk000Sub001Block159Tail surrogateDiagTailX0RatChunk000Sub001Block159
  ring

def SurrogateDiagonalTailChunk000Sub001Block159HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block159HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block159Head

def SurrogateDiagonalTailChunk000Sub001Block159MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block159MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block159Mid

def SurrogateDiagonalTailChunk000Sub001Block159TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block159TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block159Tail

theorem surrogateDiagonalTailChunk000Sub001Block159_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block159HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block159MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block159TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block159Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block159 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block159HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block159MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block159TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block159Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block159_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
