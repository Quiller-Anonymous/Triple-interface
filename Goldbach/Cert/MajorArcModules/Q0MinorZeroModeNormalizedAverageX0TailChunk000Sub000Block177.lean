import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [177,178). -/

/-- Block 177 covers tail-support indices [4425,4450) and q from 7331 to 7369. -/

def TailChunk000Sub000Block177Part000SupportExplicit : Finset ℕ :=
  ([7331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7331
    = surrogateDiagTailX0RatChunk000Sub000Block177Part000

theorem surrogateDiagonalTailChunk000Sub000Block177Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part000] using hcert

def TailChunk000Sub000Block177Part001SupportExplicit : Finset ℕ :=
  ([7333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7333
    = surrogateDiagTailX0RatChunk000Sub000Block177Part001

theorem surrogateDiagonalTailChunk000Sub000Block177Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part001] using hcert

def TailChunk000Sub000Block177Part002SupportExplicit : Finset ℕ :=
  ([7334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part002 : ℚ :=
  (117163675 : ℚ) / 51608123080704

def SurrogateDiagonalTailChunk000Sub000Block177Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7334
    = surrogateDiagTailX0RatChunk000Sub000Block177Part002

theorem surrogateDiagonalTailChunk000Sub000Block177Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part002] using hcert

def TailChunk000Sub000Block177Part003SupportExplicit : Finset ℕ :=
  ([7337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part003 : ℚ :=
  (1147223307 : ℚ) / 12001304442265600

def SurrogateDiagonalTailChunk000Sub000Block177Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7337
    = surrogateDiagTailX0RatChunk000Sub000Block177Part003

theorem surrogateDiagonalTailChunk000Sub000Block177Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part003] using hcert

def TailChunk000Sub000Block177Part004SupportExplicit : Finset ℕ :=
  ([7338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part004 : ℚ :=
  (654048528175 : ℚ) / 89213723363077248

def SurrogateDiagonalTailChunk000Sub000Block177Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7338
    = surrogateDiagTailX0RatChunk000Sub000Block177Part004

theorem surrogateDiagonalTailChunk000Sub000Block177Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part004] using hcert

def TailChunk000Sub000Block177Part005SupportExplicit : Finset ℕ :=
  ([7339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part005 : ℚ :=
  (901995339 : ℚ) / 85681205859942400

def SurrogateDiagonalTailChunk000Sub000Block177Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7339
    = surrogateDiagTailX0RatChunk000Sub000Block177Part005

theorem surrogateDiagonalTailChunk000Sub000Block177Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part005] using hcert

def TailChunk000Sub000Block177Part006SupportExplicit : Finset ℕ :=
  ([7341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part006 : ℚ :=
  (374169903725 : ℚ) / 716048858396572224

def SurrogateDiagonalTailChunk000Sub000Block177Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7341
    = surrogateDiagTailX0RatChunk000Sub000Block177Part006

theorem surrogateDiagonalTailChunk000Sub000Block177Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part006] using hcert

def TailChunk000Sub000Block177Part007SupportExplicit : Finset ℕ :=
  ([7342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part007 : ℚ :=
  (336906025 : ℚ) / 181447549463442

def SurrogateDiagonalTailChunk000Sub000Block177Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7342
    = surrogateDiagTailX0RatChunk000Sub000Block177Part007

theorem surrogateDiagonalTailChunk000Sub000Block177Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part007] using hcert

def TailChunk000Sub000Block177Part008SupportExplicit : Finset ℕ :=
  ([7343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part008 : ℚ :=
  (344819661775 : ℚ) / 3909101895634157568

def SurrogateDiagonalTailChunk000Sub000Block177Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7343
    = surrogateDiagTailX0RatChunk000Sub000Block177Part008

theorem surrogateDiagonalTailChunk000Sub000Block177Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part008] using hcert

def TailChunk000Sub000Block177Part009SupportExplicit : Finset ℕ :=
  ([7345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part009 : ℚ :=
  (492288843925 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub000Block177Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7345
    = surrogateDiagTailX0RatChunk000Sub000Block177Part009

theorem surrogateDiagonalTailChunk000Sub000Block177Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part009] using hcert

def TailChunk000Sub000Block177Part010SupportExplicit : Finset ℕ :=
  ([7346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part010 : ℚ :=
  (210795765625 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub000Block177Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7346
    = surrogateDiagTailX0RatChunk000Sub000Block177Part010

theorem surrogateDiagonalTailChunk000Sub000Block177Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part010] using hcert

def TailChunk000Sub000Block177Part011SupportExplicit : Finset ℕ :=
  ([7347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part011 : ℚ :=
  (222252089 : ℚ) / 355415606507520

def SurrogateDiagonalTailChunk000Sub000Block177Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7347
    = surrogateDiagTailX0RatChunk000Sub000Block177Part011

theorem surrogateDiagonalTailChunk000Sub000Block177Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part011] using hcert

def TailChunk000Sub000Block177Part012SupportExplicit : Finset ℕ :=
  ([7349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7349
    = surrogateDiagTailX0RatChunk000Sub000Block177Part012

theorem surrogateDiagonalTailChunk000Sub000Block177Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part012] using hcert

def TailChunk000Sub000Block177Part013SupportExplicit : Finset ℕ :=
  ([7351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block177Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7351
    = surrogateDiagTailX0RatChunk000Sub000Block177Part013

theorem surrogateDiagonalTailChunk000Sub000Block177Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part013] using hcert

def TailChunk000Sub000Block177Part014SupportExplicit : Finset ℕ :=
  ([7354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part014 : ℚ :=
  (1689703116775 : ℚ) / 456592601201628288

def SurrogateDiagonalTailChunk000Sub000Block177Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7354
    = surrogateDiagTailX0RatChunk000Sub000Block177Part014

theorem surrogateDiagonalTailChunk000Sub000Block177Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part014] using hcert

def TailChunk000Sub000Block177Part015SupportExplicit : Finset ℕ :=
  ([7355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part015 : ℚ :=
  (8559350417 : ℚ) / 9963568443225600

def SurrogateDiagonalTailChunk000Sub000Block177Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7355
    = surrogateDiagTailX0RatChunk000Sub000Block177Part015

theorem surrogateDiagonalTailChunk000Sub000Block177Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part015] using hcert

def TailChunk000Sub000Block177Part016SupportExplicit : Finset ℕ :=
  ([7357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part016 : ℚ :=
  (110344726963 : ℚ) / 157561115922000000

def SurrogateDiagonalTailChunk000Sub000Block177Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7357
    = surrogateDiagTailX0RatChunk000Sub000Block177Part016

theorem surrogateDiagonalTailChunk000Sub000Block177Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part016] using hcert

def TailChunk000Sub000Block177Part017SupportExplicit : Finset ℕ :=
  ([7358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part017 : ℚ :=
  (378732398275 : ℚ) / 81976294805524992

def SurrogateDiagonalTailChunk000Sub000Block177Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7358
    = surrogateDiagTailX0RatChunk000Sub000Block177Part017

theorem surrogateDiagonalTailChunk000Sub000Block177Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part017] using hcert

def TailChunk000Sub000Block177Part018SupportExplicit : Finset ℕ :=
  ([7359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part018 : ℚ :=
  (6654586861 : ℚ) / 3887037501649920

def SurrogateDiagonalTailChunk000Sub000Block177Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7359
    = surrogateDiagTailX0RatChunk000Sub000Block177Part018

theorem surrogateDiagonalTailChunk000Sub000Block177Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part018] using hcert

def TailChunk000Sub000Block177Part019SupportExplicit : Finset ℕ :=
  ([7361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part019 : ℚ :=
  (779958650275 : ℚ) / 1426861386935304192

def SurrogateDiagonalTailChunk000Sub000Block177Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7361
    = surrogateDiagTailX0RatChunk000Sub000Block177Part019

theorem surrogateDiagonalTailChunk000Sub000Block177Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part019] using hcert

def TailChunk000Sub000Block177Part020SupportExplicit : Finset ℕ :=
  ([7363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part020 : ℚ :=
  (120224595625 : ℚ) / 239074831765592064

def SurrogateDiagonalTailChunk000Sub000Block177Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7363
    = surrogateDiagTailX0RatChunk000Sub000Block177Part020

theorem surrogateDiagonalTailChunk000Sub000Block177Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part020] using hcert

def TailChunk000Sub000Block177Part021SupportExplicit : Finset ℕ :=
  ([7365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part021 : ℚ :=
  (28265102843 : ℚ) / 11808673710489600

def SurrogateDiagonalTailChunk000Sub000Block177Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7365
    = surrogateDiagTailX0RatChunk000Sub000Block177Part021

theorem surrogateDiagonalTailChunk000Sub000Block177Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part021] using hcert

def TailChunk000Sub000Block177Part022SupportExplicit : Finset ℕ :=
  ([7366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part022 : ℚ :=
  (400359354925 : ℚ) / 96845885268152832

def SurrogateDiagonalTailChunk000Sub000Block177Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7366
    = surrogateDiagTailX0RatChunk000Sub000Block177Part022

theorem surrogateDiagonalTailChunk000Sub000Block177Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part022] using hcert

def TailChunk000Sub000Block177Part023SupportExplicit : Finset ℕ :=
  ([7367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part023 : ℚ :=
  (3276872641525 : ℚ) / 6630657249378060288

def SurrogateDiagonalTailChunk000Sub000Block177Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7367
    = surrogateDiagTailX0RatChunk000Sub000Block177Part023

theorem surrogateDiagonalTailChunk000Sub000Block177Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part023] using hcert

def TailChunk000Sub000Block177Part024SupportExplicit : Finset ℕ :=
  ([7369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block177Part024 : ℚ :=
  (848471265625 : ℚ) / 1842321143397929472

def SurrogateDiagonalTailChunk000Sub000Block177Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7369
    = surrogateDiagTailX0RatChunk000Sub000Block177Part024

theorem surrogateDiagonalTailChunk000Sub000Block177Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block177Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block177Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block177Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block177Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block177Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block177HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block177Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part000
    + surrogateDiagTailX0RatChunk000Sub000Block177Part001
    + surrogateDiagTailX0RatChunk000Sub000Block177Part002
    + surrogateDiagTailX0RatChunk000Sub000Block177Part003
    + surrogateDiagTailX0RatChunk000Sub000Block177Part004
    + surrogateDiagTailX0RatChunk000Sub000Block177Part005
    + surrogateDiagTailX0RatChunk000Sub000Block177Part006
    + surrogateDiagTailX0RatChunk000Sub000Block177Part007
    + surrogateDiagTailX0RatChunk000Sub000Block177Part008
    + surrogateDiagTailX0RatChunk000Sub000Block177Part009

def surrogateDiagonalTailChunk000Sub000Block177MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block177Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part010
    + surrogateDiagTailX0RatChunk000Sub000Block177Part011
    + surrogateDiagTailX0RatChunk000Sub000Block177Part012
    + surrogateDiagTailX0RatChunk000Sub000Block177Part013
    + surrogateDiagTailX0RatChunk000Sub000Block177Part014
    + surrogateDiagTailX0RatChunk000Sub000Block177Part015
    + surrogateDiagTailX0RatChunk000Sub000Block177Part016
    + surrogateDiagTailX0RatChunk000Sub000Block177Part017
    + surrogateDiagTailX0RatChunk000Sub000Block177Part018
    + surrogateDiagTailX0RatChunk000Sub000Block177Part019

def surrogateDiagonalTailChunk000Sub000Block177TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block177Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part020
    + surrogateDiagTailX0RatChunk000Sub000Block177Part021
    + surrogateDiagTailX0RatChunk000Sub000Block177Part022
    + surrogateDiagTailX0RatChunk000Sub000Block177Part023
    + surrogateDiagTailX0RatChunk000Sub000Block177Part024

def surrogateDiagonalTailChunk000Sub000Block177Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block177HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block177MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block177TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block177 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block177Part000
    + surrogateDiagTailX0RatChunk000Sub000Block177Part001
    + surrogateDiagTailX0RatChunk000Sub000Block177Part002
    + surrogateDiagTailX0RatChunk000Sub000Block177Part003
    + surrogateDiagTailX0RatChunk000Sub000Block177Part004
    + surrogateDiagTailX0RatChunk000Sub000Block177Part005
    + surrogateDiagTailX0RatChunk000Sub000Block177Part006
    + surrogateDiagTailX0RatChunk000Sub000Block177Part007
    + surrogateDiagTailX0RatChunk000Sub000Block177Part008
    + surrogateDiagTailX0RatChunk000Sub000Block177Part009
    + surrogateDiagTailX0RatChunk000Sub000Block177Part010
    + surrogateDiagTailX0RatChunk000Sub000Block177Part011
    + surrogateDiagTailX0RatChunk000Sub000Block177Part012
    + surrogateDiagTailX0RatChunk000Sub000Block177Part013
    + surrogateDiagTailX0RatChunk000Sub000Block177Part014
    + surrogateDiagTailX0RatChunk000Sub000Block177Part015
    + surrogateDiagTailX0RatChunk000Sub000Block177Part016
    + surrogateDiagTailX0RatChunk000Sub000Block177Part017
    + surrogateDiagTailX0RatChunk000Sub000Block177Part018
    + surrogateDiagTailX0RatChunk000Sub000Block177Part019
    + surrogateDiagTailX0RatChunk000Sub000Block177Part020
    + surrogateDiagTailX0RatChunk000Sub000Block177Part021
    + surrogateDiagTailX0RatChunk000Sub000Block177Part022
    + surrogateDiagTailX0RatChunk000Sub000Block177Part023
    + surrogateDiagTailX0RatChunk000Sub000Block177Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block177_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block177Head + surrogateDiagTailX0RatChunk000Sub000Block177Mid + surrogateDiagTailX0RatChunk000Sub000Block177Tail =
      surrogateDiagTailX0RatChunk000Sub000Block177 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block177Head surrogateDiagTailX0RatChunk000Sub000Block177Mid surrogateDiagTailX0RatChunk000Sub000Block177Tail surrogateDiagTailX0RatChunk000Sub000Block177
  ring

def SurrogateDiagonalTailChunk000Sub000Block177HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block177HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block177Head

def SurrogateDiagonalTailChunk000Sub000Block177MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block177MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block177Mid

def SurrogateDiagonalTailChunk000Sub000Block177TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block177TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block177Tail

theorem surrogateDiagonalTailChunk000Sub000Block177_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block177HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block177MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block177TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block177Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block177 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block177HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block177MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block177TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block177Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block177_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
