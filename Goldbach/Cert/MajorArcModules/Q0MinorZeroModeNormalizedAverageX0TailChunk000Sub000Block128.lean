import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [128,129). -/

/- Block 128 covers tail-support indices [3200,3225) and q from 5315 to 5358. -/

def TailChunk000Sub000Block128Part000SupportExplicit : Finset ℕ :=
  ([5315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part000 : ℚ :=
  (705668480375 : ℚ) / 407131678321173504

def SurrogateDiagonalTailChunk000Sub000Block128Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5315
    = surrogateDiagTailX0RatChunk000Sub000Block128Part000

theorem surrogateDiagonalTailChunk000Sub000Block128Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part000] using hcert

def TailChunk000Sub000Block128Part001SupportExplicit : Finset ℕ :=
  ([5317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part001 : ℚ :=
  (64162436675 : ℚ) / 718393674637246464

def SurrogateDiagonalTailChunk000Sub000Block128Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5317
    = surrogateDiagTailX0RatChunk000Sub000Block128Part001

theorem surrogateDiagonalTailChunk000Sub000Block128Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part001] using hcert

def TailChunk000Sub000Block128Part002SupportExplicit : Finset ℕ :=
  ([5318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part002 : ℚ :=
  (110473140625 : ℚ) / 31202311915350162

def SurrogateDiagonalTailChunk000Sub000Block128Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5318
    = surrogateDiagTailX0RatChunk000Sub000Block128Part002

theorem surrogateDiagonalTailChunk000Sub000Block128Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part002] using hcert

def TailChunk000Sub000Block128Part003SupportExplicit : Finset ℕ :=
  ([5321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part003 : ℚ :=
  (827037375425 : ℚ) / 776417239602561024

def SurrogateDiagonalTailChunk000Sub000Block128Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5321
    = surrogateDiagTailX0RatChunk000Sub000Block128Part003

theorem surrogateDiagonalTailChunk000Sub000Block128Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part003] using hcert

def TailChunk000Sub000Block128Part004SupportExplicit : Finset ℕ :=
  ([5322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part004 : ℚ :=
  (117874275 : ℚ) / 4929749760128

def SurrogateDiagonalTailChunk000Sub000Block128Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5322
    = surrogateDiagTailX0RatChunk000Sub000Block128Part004

theorem surrogateDiagonalTailChunk000Sub000Block128Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part004] using hcert

def TailChunk000Sub000Block128Part005SupportExplicit : Finset ℕ :=
  ([5323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part005 : ℚ :=
  (442723890625 : ℚ) / 501494700966826482

def SurrogateDiagonalTailChunk000Sub000Block128Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5323
    = surrogateDiagTailX0RatChunk000Sub000Block128Part005

theorem surrogateDiagonalTailChunk000Sub000Block128Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part005] using hcert

def TailChunk000Sub000Block128Part006SupportExplicit : Finset ℕ :=
  ([5326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part006 : ℚ :=
  (886268835775 : ℚ) / 125562242495853768

def SurrogateDiagonalTailChunk000Sub000Block128Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5326
    = surrogateDiagTailX0RatChunk000Sub000Block128Part006

theorem surrogateDiagonalTailChunk000Sub000Block128Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part006] using hcert

def TailChunk000Sub000Block128Part007SupportExplicit : Finset ℕ :=
  ([5327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part007 : ℚ :=
  (59290438927 : ℚ) / 43246027572019200

def SurrogateDiagonalTailChunk000Sub000Block128Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5327
    = surrogateDiagTailX0RatChunk000Sub000Block128Part007

theorem surrogateDiagonalTailChunk000Sub000Block128Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part007] using hcert

def TailChunk000Sub000Block128Part008SupportExplicit : Finset ℕ :=
  ([5330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part008 : ℚ :=
  (3103276901 : ℚ) / 169903285862400

def SurrogateDiagonalTailChunk000Sub000Block128Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5330
    = surrogateDiagTailX0RatChunk000Sub000Block128Part008

theorem surrogateDiagonalTailChunk000Sub000Block128Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part008] using hcert

def TailChunk000Sub000Block128Part009SupportExplicit : Finset ℕ :=
  ([5331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part009 : ℚ :=
  (39448025 : ℚ) / 13265101651968

def SurrogateDiagonalTailChunk000Sub000Block128Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5331
    = surrogateDiagTailX0RatChunk000Sub000Block128Part009

theorem surrogateDiagonalTailChunk000Sub000Block128Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part009] using hcert

def TailChunk000Sub000Block128Part010SupportExplicit : Finset ℕ :=
  ([5333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part010 : ℚ :=
  (444388890625 : ℚ) / 505274557635946272

def SurrogateDiagonalTailChunk000Sub000Block128Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5333
    = surrogateDiagTailX0RatChunk000Sub000Block128Part010

theorem surrogateDiagonalTailChunk000Sub000Block128Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part010] using hcert

def TailChunk000Sub000Block128Part011SupportExplicit : Finset ℕ :=
  ([5334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part011 : ℚ :=
  (16595275 : ℚ) / 435537865728

def SurrogateDiagonalTailChunk000Sub000Block128Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5334
    = surrogateDiagTailX0RatChunk000Sub000Block128Part011

theorem surrogateDiagonalTailChunk000Sub000Block128Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part011] using hcert

def TailChunk000Sub000Block128Part012SupportExplicit : Finset ℕ :=
  ([5335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part012 : ℚ :=
  (51124059091 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block128Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5335
    = surrogateDiagTailX0RatChunk000Sub000Block128Part012

theorem surrogateDiagonalTailChunk000Sub000Block128Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part012] using hcert

def TailChunk000Sub000Block128Part013SupportExplicit : Finset ℕ :=
  ([5338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part013 : ℚ :=
  (414755462825 : ℚ) / 48526077475160064

def SurrogateDiagonalTailChunk000Sub000Block128Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5338
    = surrogateDiagTailX0RatChunk000Sub000Block128Part013

theorem surrogateDiagonalTailChunk000Sub000Block128Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part013] using hcert

def TailChunk000Sub000Block128Part014SupportExplicit : Finset ℕ :=
  ([5339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part014 : ℚ :=
  (5589449491 : ℚ) / 5378086090137600

def SurrogateDiagonalTailChunk000Sub000Block128Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5339
    = surrogateDiagTailX0RatChunk000Sub000Block128Part014

theorem surrogateDiagonalTailChunk000Sub000Block128Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part014] using hcert

def TailChunk000Sub000Block128Part015SupportExplicit : Finset ℕ :=
  ([5342] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part015 : ℚ :=
  (35664070759 : ℚ) / 5083137945304200

def SurrogateDiagonalTailChunk000Sub000Block128Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5342
    = surrogateDiagTailX0RatChunk000Sub000Block128Part015

theorem surrogateDiagonalTailChunk000Sub000Block128Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part015] using hcert

def TailChunk000Sub000Block128Part016SupportExplicit : Finset ℕ :=
  ([5343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part016 : ℚ :=
  (361297442975 : ℚ) / 94603282256756736

def SurrogateDiagonalTailChunk000Sub000Block128Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5343
    = surrogateDiagTailX0RatChunk000Sub000Block128Part016

theorem surrogateDiagonalTailChunk000Sub000Block128Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part016] using hcert

def TailChunk000Sub000Block128Part017SupportExplicit : Finset ℕ :=
  ([5345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part017 : ℚ :=
  (713657577875 : ℚ) / 416410660479320064

def SurrogateDiagonalTailChunk000Sub000Block128Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5345
    = surrogateDiagTailX0RatChunk000Sub000Block128Part017

theorem surrogateDiagonalTailChunk000Sub000Block128Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part017] using hcert

def TailChunk000Sub000Block128Part018SupportExplicit : Finset ℕ :=
  ([5347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part018 : ℚ :=
  (446725140625 : ℚ) / 510602204171240082

def SurrogateDiagonalTailChunk000Sub000Block128Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5347
    = surrogateDiagTailX0RatChunk000Sub000Block128Part018

theorem surrogateDiagonalTailChunk000Sub000Block128Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part018] using hcert

def TailChunk000Sub000Block128Part019SupportExplicit : Finset ℕ :=
  ([5349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part019 : ℚ :=
  (39714875 : ℚ) / 13445270232768

def SurrogateDiagonalTailChunk000Sub000Block128Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5349
    = surrogateDiagTailX0RatChunk000Sub000Block128Part019

theorem surrogateDiagonalTailChunk000Sub000Block128Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part019] using hcert

def TailChunk000Sub000Block128Part020SupportExplicit : Finset ℕ :=
  ([5351] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part020 : ℚ :=
  (28633201 : ℚ) / 32776454230050

def SurrogateDiagonalTailChunk000Sub000Block128Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5351
    = surrogateDiagTailX0RatChunk000Sub000Block128Part020

theorem surrogateDiagonalTailChunk000Sub000Block128Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part020] using hcert

def TailChunk000Sub000Block128Part021SupportExplicit : Finset ℕ :=
  ([5353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part021 : ℚ :=
  (17371610209 : ℚ) / 18282695808000000

def SurrogateDiagonalTailChunk000Sub000Block128Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5353
    = surrogateDiagTailX0RatChunk000Sub000Block128Part021

theorem surrogateDiagonalTailChunk000Sub000Block128Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part021] using hcert

def TailChunk000Sub000Block128Part022SupportExplicit : Finset ℕ :=
  ([5354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part022 : ℚ :=
  (895611966775 : ℚ) / 128224582970076288

def SurrogateDiagonalTailChunk000Sub000Block128Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5354
    = surrogateDiagTailX0RatChunk000Sub000Block128Part022

theorem surrogateDiagonalTailChunk000Sub000Block128Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part022] using hcert

def TailChunk000Sub000Block128Part023SupportExplicit : Finset ℕ :=
  ([5357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part023 : ℚ :=
  (10750172251 : ℚ) / 9299951354347200

def SurrogateDiagonalTailChunk000Sub000Block128Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5357
    = surrogateDiagTailX0RatChunk000Sub000Block128Part023

theorem surrogateDiagonalTailChunk000Sub000Block128Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part023] using hcert

def TailChunk000Sub000Block128Part024SupportExplicit : Finset ℕ :=
  ([5358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block128Part024 : ℚ :=
  (275812271525 : ℚ) / 9402388522804224

def SurrogateDiagonalTailChunk000Sub000Block128Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5358
    = surrogateDiagTailX0RatChunk000Sub000Block128Part024

theorem surrogateDiagonalTailChunk000Sub000Block128Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block128Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block128Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block128Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block128Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block128Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block128Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block128HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block128Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block128Part000
    + surrogateDiagTailX0RatChunk000Sub000Block128Part001
    + surrogateDiagTailX0RatChunk000Sub000Block128Part002
    + surrogateDiagTailX0RatChunk000Sub000Block128Part003
    + surrogateDiagTailX0RatChunk000Sub000Block128Part004
    + surrogateDiagTailX0RatChunk000Sub000Block128Part005
    + surrogateDiagTailX0RatChunk000Sub000Block128Part006
    + surrogateDiagTailX0RatChunk000Sub000Block128Part007
    + surrogateDiagTailX0RatChunk000Sub000Block128Part008
    + surrogateDiagTailX0RatChunk000Sub000Block128Part009

def surrogateDiagonalTailChunk000Sub000Block128MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block128Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block128Part010
    + surrogateDiagTailX0RatChunk000Sub000Block128Part011
    + surrogateDiagTailX0RatChunk000Sub000Block128Part012
    + surrogateDiagTailX0RatChunk000Sub000Block128Part013
    + surrogateDiagTailX0RatChunk000Sub000Block128Part014
    + surrogateDiagTailX0RatChunk000Sub000Block128Part015
    + surrogateDiagTailX0RatChunk000Sub000Block128Part016
    + surrogateDiagTailX0RatChunk000Sub000Block128Part017
    + surrogateDiagTailX0RatChunk000Sub000Block128Part018
    + surrogateDiagTailX0RatChunk000Sub000Block128Part019

def surrogateDiagonalTailChunk000Sub000Block128TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block128Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block128Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block128Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block128Part020
    + surrogateDiagTailX0RatChunk000Sub000Block128Part021
    + surrogateDiagTailX0RatChunk000Sub000Block128Part022
    + surrogateDiagTailX0RatChunk000Sub000Block128Part023
    + surrogateDiagTailX0RatChunk000Sub000Block128Part024

def surrogateDiagonalTailChunk000Sub000Block128Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block128HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block128MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block128TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block128 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block128Part000
    + surrogateDiagTailX0RatChunk000Sub000Block128Part001
    + surrogateDiagTailX0RatChunk000Sub000Block128Part002
    + surrogateDiagTailX0RatChunk000Sub000Block128Part003
    + surrogateDiagTailX0RatChunk000Sub000Block128Part004
    + surrogateDiagTailX0RatChunk000Sub000Block128Part005
    + surrogateDiagTailX0RatChunk000Sub000Block128Part006
    + surrogateDiagTailX0RatChunk000Sub000Block128Part007
    + surrogateDiagTailX0RatChunk000Sub000Block128Part008
    + surrogateDiagTailX0RatChunk000Sub000Block128Part009
    + surrogateDiagTailX0RatChunk000Sub000Block128Part010
    + surrogateDiagTailX0RatChunk000Sub000Block128Part011
    + surrogateDiagTailX0RatChunk000Sub000Block128Part012
    + surrogateDiagTailX0RatChunk000Sub000Block128Part013
    + surrogateDiagTailX0RatChunk000Sub000Block128Part014
    + surrogateDiagTailX0RatChunk000Sub000Block128Part015
    + surrogateDiagTailX0RatChunk000Sub000Block128Part016
    + surrogateDiagTailX0RatChunk000Sub000Block128Part017
    + surrogateDiagTailX0RatChunk000Sub000Block128Part018
    + surrogateDiagTailX0RatChunk000Sub000Block128Part019
    + surrogateDiagTailX0RatChunk000Sub000Block128Part020
    + surrogateDiagTailX0RatChunk000Sub000Block128Part021
    + surrogateDiagTailX0RatChunk000Sub000Block128Part022
    + surrogateDiagTailX0RatChunk000Sub000Block128Part023
    + surrogateDiagTailX0RatChunk000Sub000Block128Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block128_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block128Head + surrogateDiagTailX0RatChunk000Sub000Block128Mid + surrogateDiagTailX0RatChunk000Sub000Block128Tail =
      surrogateDiagTailX0RatChunk000Sub000Block128 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block128Head surrogateDiagTailX0RatChunk000Sub000Block128Mid surrogateDiagTailX0RatChunk000Sub000Block128Tail surrogateDiagTailX0RatChunk000Sub000Block128
  ring

def SurrogateDiagonalTailChunk000Sub000Block128HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block128HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block128Head

def SurrogateDiagonalTailChunk000Sub000Block128MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block128MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block128Mid

def SurrogateDiagonalTailChunk000Sub000Block128TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block128TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block128Tail

theorem surrogateDiagonalTailChunk000Sub000Block128_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block128HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block128MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block128TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block128Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block128 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block128HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block128MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block128TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block128Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block128_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
