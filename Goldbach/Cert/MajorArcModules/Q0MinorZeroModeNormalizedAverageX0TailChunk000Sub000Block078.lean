import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [78,79). -/

/- Block 078 covers tail-support indices [1950,1975) and q from 3257 to 3297. -/

def TailChunk000Sub000Block078Part000SupportExplicit : Finset ℕ :=
  ([3257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part000 : ℚ :=
  (1325740923775 : ℚ) / 281037610181019648

def SurrogateDiagonalTailChunk000Sub000Block078Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3257
    = surrogateDiagTailX0RatChunk000Sub000Block078Part000

theorem surrogateDiagonalTailChunk000Sub000Block078Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part000] using hcert

def TailChunk000Sub000Block078Part001SupportExplicit : Finset ℕ :=
  ([3259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part001 : ℚ :=
  (165954390625 : ℚ) / 70432189189923762

def SurrogateDiagonalTailChunk000Sub000Block078Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3259
    = surrogateDiagTailX0RatChunk000Sub000Block078Part001

theorem surrogateDiagonalTailChunk000Sub000Block078Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part001] using hcert

def TailChunk000Sub000Block078Part002SupportExplicit : Finset ℕ :=
  ([3261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part002 : ℚ :=
  (590381611075 : ℚ) / 55650124792038528

def SurrogateDiagonalTailChunk000Sub000Block078Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3261
    = surrogateDiagTailX0RatChunk000Sub000Block078Part002

theorem surrogateDiagonalTailChunk000Sub000Block078Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part002] using hcert

def TailChunk000Sub000Block078Part003SupportExplicit : Finset ℕ :=
  ([3262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part003 : ℚ :=
  (214589828825 : ℚ) / 4694115856564224

def SurrogateDiagonalTailChunk000Sub000Block078Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3262
    = surrogateDiagTailX0RatChunk000Sub000Block078Part003

theorem surrogateDiagonalTailChunk000Sub000Block078Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part003] using hcert

def TailChunk000Sub000Block078Part004SupportExplicit : Finset ℕ :=
  ([3263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part004 : ℚ :=
  (25466187397 : ℚ) / 8101620000000000

def SurrogateDiagonalTailChunk000Sub000Block078Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3263
    = surrogateDiagTailX0RatChunk000Sub000Block078Part004

theorem surrogateDiagonalTailChunk000Sub000Block078Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part004] using hcert

def TailChunk000Sub000Block078Part005SupportExplicit : Finset ℕ :=
  ([3265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part005 : ℚ :=
  (153102715675 : ℚ) / 28919928559706112

def SurrogateDiagonalTailChunk000Sub000Block078Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3265
    = surrogateDiagTailX0RatChunk000Sub000Block078Part005

theorem surrogateDiagonalTailChunk000Sub000Block078Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part005] using hcert

def TailChunk000Sub000Block078Part006SupportExplicit : Finset ℕ :=
  ([3266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part006 : ℚ :=
  (1180141021 : ℚ) / 35160071608200

def SurrogateDiagonalTailChunk000Sub000Block078Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3266
    = surrogateDiagTailX0RatChunk000Sub000Block078Part006

theorem surrogateDiagonalTailChunk000Sub000Block078Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part006] using hcert

def TailChunk000Sub000Block078Part007SupportExplicit : Finset ℕ :=
  ([3269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part007 : ℚ :=
  (122379692125 : ℚ) / 16979817485400192

def SurrogateDiagonalTailChunk000Sub000Block078Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3269
    = surrogateDiagTailX0RatChunk000Sub000Block078Part007

theorem surrogateDiagonalTailChunk000Sub000Block078Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part007] using hcert

def TailChunk000Sub000Block078Part008SupportExplicit : Finset ℕ :=
  ([3270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part008 : ℚ :=
  (16606219675 : ℚ) / 87088707698688

def SurrogateDiagonalTailChunk000Sub000Block078Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3270
    = surrogateDiagTailX0RatChunk000Sub000Block078Part008

theorem surrogateDiagonalTailChunk000Sub000Block078Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part008] using hcert

def TailChunk000Sub000Block078Part009SupportExplicit : Finset ℕ :=
  ([3271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part009 : ℚ :=
  (53486505559 : ℚ) / 11436097803208200

def SurrogateDiagonalTailChunk000Sub000Block078Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3271
    = surrogateDiagTailX0RatChunk000Sub000Block078Part009

theorem surrogateDiagonalTailChunk000Sub000Block078Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part009] using hcert

def TailChunk000Sub000Block078Part010SupportExplicit : Finset ℕ :=
  ([3273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part010 : ℚ :=
  (14865522467 : ℚ) / 1129491141057600

def SurrogateDiagonalTailChunk000Sub000Block078Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3273
    = surrogateDiagTailX0RatChunk000Sub000Block078Part010

theorem surrogateDiagonalTailChunk000Sub000Block078Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part010] using hcert

def TailChunk000Sub000Block078Part011SupportExplicit : Finset ℕ :=
  ([3274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part011 : ℚ :=
  (167418568275 : ℚ) / 5970886303486336

def SurrogateDiagonalTailChunk000Sub000Block078Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3274
    = surrogateDiagTailX0RatChunk000Sub000Block078Part011

theorem surrogateDiagonalTailChunk000Sub000Block078Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part011] using hcert

def TailChunk000Sub000Block078Part012SupportExplicit : Finset ℕ :=
  ([3277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part012 : ℚ :=
  (423960000525 : ℚ) / 80613879196942336

def SurrogateDiagonalTailChunk000Sub000Block078Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3277
    = surrogateDiagTailX0RatChunk000Sub000Block078Part012

theorem surrogateDiagonalTailChunk000Sub000Block078Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part012] using hcert

def TailChunk000Sub000Block078Part013SupportExplicit : Finset ℕ :=
  ([3278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part013 : ℚ :=
  (1216899051 : ℚ) / 31992078202880

def SurrogateDiagonalTailChunk000Sub000Block078Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3278
    = surrogateDiagTailX0RatChunk000Sub000Block078Part013

theorem surrogateDiagonalTailChunk000Sub000Block078Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part013] using hcert

def TailChunk000Sub000Block078Part014SupportExplicit : Finset ℕ :=
  ([3279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part014 : ℚ :=
  (820592593075 : ℚ) / 56890191414970368

def SurrogateDiagonalTailChunk000Sub000Block078Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3279
    = surrogateDiagTailX0RatChunk000Sub000Block078Part014

theorem surrogateDiagonalTailChunk000Sub000Block078Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part014] using hcert

def TailChunk000Sub000Block078Part015SupportExplicit : Finset ℕ :=
  ([3281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part015 : ℚ :=
  (217499173825 : ℚ) / 74231878281854976

def SurrogateDiagonalTailChunk000Sub000Block078Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3281
    = surrogateDiagTailX0RatChunk000Sub000Block078Part015

theorem surrogateDiagonalTailChunk000Sub000Block078Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part015] using hcert

def TailChunk000Sub000Block078Part016SupportExplicit : Finset ℕ :=
  ([3282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part016 : ℚ :=
  (430775 : ℚ) / 4557597408

def SurrogateDiagonalTailChunk000Sub000Block078Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3282
    = surrogateDiagTailX0RatChunk000Sub000Block078Part016

theorem surrogateDiagonalTailChunk000Sub000Block078Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part016] using hcert

def TailChunk000Sub000Block078Part017SupportExplicit : Finset ℕ :=
  ([3286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part017 : ℚ :=
  (128300891 : ℚ) / 3949062294528

def SurrogateDiagonalTailChunk000Sub000Block078Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3286
    = surrogateDiagTailX0RatChunk000Sub000Block078Part017

theorem surrogateDiagonalTailChunk000Sub000Block078Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part017] using hcert

def TailChunk000Sub000Block078Part018SupportExplicit : Finset ℕ :=
  ([3287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part018 : ℚ :=
  (656541926125 : ℚ) / 229736852599523328

def SurrogateDiagonalTailChunk000Sub000Block078Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3287
    = surrogateDiagTailX0RatChunk000Sub000Block078Part018

theorem surrogateDiagonalTailChunk000Sub000Block078Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part018] using hcert

def TailChunk000Sub000Block078Part019SupportExplicit : Finset ℕ :=
  ([3289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part019 : ℚ :=
  (727736077 : ℚ) / 147227391590400

def SurrogateDiagonalTailChunk000Sub000Block078Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3289
    = surrogateDiagTailX0RatChunk000Sub000Block078Part019

theorem surrogateDiagonalTailChunk000Sub000Block078Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part019] using hcert

def TailChunk000Sub000Block078Part020SupportExplicit : Finset ℕ :=
  ([3290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part020 : ℚ :=
  (170408937875 : ℚ) / 1857261930430464

def SurrogateDiagonalTailChunk000Sub000Block078Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3290
    = surrogateDiagTailX0RatChunk000Sub000Block078Part020

theorem surrogateDiagonalTailChunk000Sub000Block078Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part020] using hcert

def TailChunk000Sub000Block078Part021SupportExplicit : Finset ℕ :=
  ([3291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part021 : ℚ :=
  (826610686975 : ℚ) / 57728338505269248

def SurrogateDiagonalTailChunk000Sub000Block078Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3291
    = surrogateDiagTailX0RatChunk000Sub000Block078Part021

theorem surrogateDiagonalTailChunk000Sub000Block078Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part021] using hcert

def TailChunk000Sub000Block078Part022SupportExplicit : Finset ℕ :=
  ([3293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part022 : ℚ :=
  (1292451289825 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub000Block078Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3293
    = surrogateDiagTailX0RatChunk000Sub000Block078Part022

theorem surrogateDiagonalTailChunk000Sub000Block078Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part022] using hcert

def TailChunk000Sub000Block078Part023SupportExplicit : Finset ℕ :=
  ([3295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part023 : ℚ :=
  (343240816725 : ℚ) / 39999000930359296

def SurrogateDiagonalTailChunk000Sub000Block078Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3295
    = surrogateDiagTailX0RatChunk000Sub000Block078Part023

theorem surrogateDiagonalTailChunk000Sub000Block078Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part023] using hcert

def TailChunk000Sub000Block078Part024SupportExplicit : Finset ℕ :=
  ([3297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block078Part024 : ℚ :=
  (6373123075 : ℚ) / 284332485206016

def SurrogateDiagonalTailChunk000Sub000Block078Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3297
    = surrogateDiagTailX0RatChunk000Sub000Block078Part024

theorem surrogateDiagonalTailChunk000Sub000Block078Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block078Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block078Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block078Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block078Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block078Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block078HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block078Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block078Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block078Part000
    + surrogateDiagTailX0RatChunk000Sub000Block078Part001
    + surrogateDiagTailX0RatChunk000Sub000Block078Part002
    + surrogateDiagTailX0RatChunk000Sub000Block078Part003
    + surrogateDiagTailX0RatChunk000Sub000Block078Part004
    + surrogateDiagTailX0RatChunk000Sub000Block078Part005
    + surrogateDiagTailX0RatChunk000Sub000Block078Part006
    + surrogateDiagTailX0RatChunk000Sub000Block078Part007
    + surrogateDiagTailX0RatChunk000Sub000Block078Part008
    + surrogateDiagTailX0RatChunk000Sub000Block078Part009

def surrogateDiagonalTailChunk000Sub000Block078MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block078Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block078Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block078Part010
    + surrogateDiagTailX0RatChunk000Sub000Block078Part011
    + surrogateDiagTailX0RatChunk000Sub000Block078Part012
    + surrogateDiagTailX0RatChunk000Sub000Block078Part013
    + surrogateDiagTailX0RatChunk000Sub000Block078Part014
    + surrogateDiagTailX0RatChunk000Sub000Block078Part015
    + surrogateDiagTailX0RatChunk000Sub000Block078Part016
    + surrogateDiagTailX0RatChunk000Sub000Block078Part017
    + surrogateDiagTailX0RatChunk000Sub000Block078Part018
    + surrogateDiagTailX0RatChunk000Sub000Block078Part019

def surrogateDiagonalTailChunk000Sub000Block078TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block078Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block078Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block078Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block078Part020
    + surrogateDiagTailX0RatChunk000Sub000Block078Part021
    + surrogateDiagTailX0RatChunk000Sub000Block078Part022
    + surrogateDiagTailX0RatChunk000Sub000Block078Part023
    + surrogateDiagTailX0RatChunk000Sub000Block078Part024

def surrogateDiagonalTailChunk000Sub000Block078Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block078HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block078MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block078TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block078 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block078Part000
    + surrogateDiagTailX0RatChunk000Sub000Block078Part001
    + surrogateDiagTailX0RatChunk000Sub000Block078Part002
    + surrogateDiagTailX0RatChunk000Sub000Block078Part003
    + surrogateDiagTailX0RatChunk000Sub000Block078Part004
    + surrogateDiagTailX0RatChunk000Sub000Block078Part005
    + surrogateDiagTailX0RatChunk000Sub000Block078Part006
    + surrogateDiagTailX0RatChunk000Sub000Block078Part007
    + surrogateDiagTailX0RatChunk000Sub000Block078Part008
    + surrogateDiagTailX0RatChunk000Sub000Block078Part009
    + surrogateDiagTailX0RatChunk000Sub000Block078Part010
    + surrogateDiagTailX0RatChunk000Sub000Block078Part011
    + surrogateDiagTailX0RatChunk000Sub000Block078Part012
    + surrogateDiagTailX0RatChunk000Sub000Block078Part013
    + surrogateDiagTailX0RatChunk000Sub000Block078Part014
    + surrogateDiagTailX0RatChunk000Sub000Block078Part015
    + surrogateDiagTailX0RatChunk000Sub000Block078Part016
    + surrogateDiagTailX0RatChunk000Sub000Block078Part017
    + surrogateDiagTailX0RatChunk000Sub000Block078Part018
    + surrogateDiagTailX0RatChunk000Sub000Block078Part019
    + surrogateDiagTailX0RatChunk000Sub000Block078Part020
    + surrogateDiagTailX0RatChunk000Sub000Block078Part021
    + surrogateDiagTailX0RatChunk000Sub000Block078Part022
    + surrogateDiagTailX0RatChunk000Sub000Block078Part023
    + surrogateDiagTailX0RatChunk000Sub000Block078Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block078_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block078Head + surrogateDiagTailX0RatChunk000Sub000Block078Mid + surrogateDiagTailX0RatChunk000Sub000Block078Tail =
      surrogateDiagTailX0RatChunk000Sub000Block078 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block078Head surrogateDiagTailX0RatChunk000Sub000Block078Mid surrogateDiagTailX0RatChunk000Sub000Block078Tail surrogateDiagTailX0RatChunk000Sub000Block078
  ring

def SurrogateDiagonalTailChunk000Sub000Block078HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block078HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block078Head

def SurrogateDiagonalTailChunk000Sub000Block078MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block078MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block078Mid

def SurrogateDiagonalTailChunk000Sub000Block078TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block078TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block078Tail

theorem surrogateDiagonalTailChunk000Sub000Block078_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block078HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block078MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block078TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block078Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block078 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block078HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block078MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block078TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block078Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block078_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
