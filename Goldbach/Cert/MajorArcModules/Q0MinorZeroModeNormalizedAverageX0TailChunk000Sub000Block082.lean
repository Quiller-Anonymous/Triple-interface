import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [82,83). -/

/- Block 082 covers tail-support indices [2050,2075) and q from 3417 to 3457. -/

def TailChunk000Sub000Block082Part000SupportExplicit : Finset ℕ :=
  ([3417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part000 : ℚ :=
  (303071675675 : ℚ) / 24875540083113984

def SurrogateDiagonalTailChunk000Sub000Block082Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3417
    = surrogateDiagTailX0RatChunk000Sub000Block082Part000

theorem surrogateDiagonalTailChunk000Sub000Block082Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part000] using hcert

def TailChunk000Sub000Block082Part001SupportExplicit : Finset ℕ :=
  ([3418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part001 : ℚ :=
  (3723868275 : ℚ) / 144764138291584

def SurrogateDiagonalTailChunk000Sub000Block082Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3418
    = surrogateDiagTailX0RatChunk000Sub000Block082Part001

theorem surrogateDiagonalTailChunk000Sub000Block082Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part001] using hcert

def TailChunk000Sub000Block082Part002SupportExplicit : Finset ℕ :=
  ([3419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part002 : ℚ :=
  (698872343725 : ℚ) / 244318868477134848

def SurrogateDiagonalTailChunk000Sub000Block082Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3419
    = surrogateDiagTailX0RatChunk000Sub000Block082Part002

theorem surrogateDiagonalTailChunk000Sub000Block082Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part002] using hcert

def TailChunk000Sub000Block082Part003SupportExplicit : Finset ℕ :=
  ([3421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part003 : ℚ :=
  (1110316519 : ℚ) / 369482281680000

def SurrogateDiagonalTailChunk000Sub000Block082Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3421
    = surrogateDiagTailX0RatChunk000Sub000Block082Part003

theorem surrogateDiagonalTailChunk000Sub000Block082Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part003] using hcert

def TailChunk000Sub000Block082Part004SupportExplicit : Finset ℕ :=
  ([3422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part004 : ℚ :=
  (520430038225 : ℚ) / 17392858289522688

def SurrogateDiagonalTailChunk000Sub000Block082Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3422
    = surrogateDiagTailX0RatChunk000Sub000Block082Part004

theorem surrogateDiagonalTailChunk000Sub000Block082Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part004] using hcert

def TailChunk000Sub000Block082Part005SupportExplicit : Finset ℕ :=
  ([3423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part005 : ℚ :=
  (195113975 : ℚ) / 13777705710144

def SurrogateDiagonalTailChunk000Sub000Block082Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3423
    = surrogateDiagTailX0RatChunk000Sub000Block082Part005

theorem surrogateDiagonalTailChunk000Sub000Block082Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part005] using hcert

def TailChunk000Sub000Block082Part006SupportExplicit : Finset ℕ :=
  ([3426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part006 : ℚ :=
  (244091 : ℚ) / 2814933600

def SurrogateDiagonalTailChunk000Sub000Block082Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3426
    = surrogateDiagTailX0RatChunk000Sub000Block082Part006

theorem surrogateDiagonalTailChunk000Sub000Block082Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part006] using hcert

def TailChunk000Sub000Block082Part007SupportExplicit : Finset ℕ :=
  ([3427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part007 : ℚ :=
  (344008875025 : ℚ) / 70259402545254912

def SurrogateDiagonalTailChunk000Sub000Block082Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3427
    = surrogateDiagTailX0RatChunk000Sub000Block082Part007

theorem surrogateDiagonalTailChunk000Sub000Block082Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part007] using hcert

def TailChunk000Sub000Block082Part008SupportExplicit : Finset ℕ :=
  ([3431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part008 : ℚ :=
  (234473866325 : ℚ) / 50146072121622528

def SurrogateDiagonalTailChunk000Sub000Block082Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3431
    = surrogateDiagTailX0RatChunk000Sub000Block082Part008

theorem surrogateDiagonalTailChunk000Sub000Block082Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part008] using hcert

def TailChunk000Sub000Block082Part009SupportExplicit : Finset ℕ :=
  ([3433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part009 : ℚ :=
  (1472891487775 : ℚ) / 346909326325106688

def SurrogateDiagonalTailChunk000Sub000Block082Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3433
    = surrogateDiagTailX0RatChunk000Sub000Block082Part009

theorem surrogateDiagonalTailChunk000Sub000Block082Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part009] using hcert

def TailChunk000Sub000Block082Part010SupportExplicit : Finset ℕ :=
  ([3434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part010 : ℚ :=
  (2057699917 : ℚ) / 65549107200000

def SurrogateDiagonalTailChunk000Sub000Block082Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3434
    = surrogateDiagTailX0RatChunk000Sub000Block082Part010

theorem surrogateDiagonalTailChunk000Sub000Block082Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part010] using hcert

def TailChunk000Sub000Block082Part011SupportExplicit : Finset ℕ :=
  ([3435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part011 : ℚ :=
  (688157470075 : ℚ) / 27677457646092288

def SurrogateDiagonalTailChunk000Sub000Block082Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3435
    = surrogateDiagTailX0RatChunk000Sub000Block082Part011

theorem surrogateDiagonalTailChunk000Sub000Block082Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part011] using hcert

def TailChunk000Sub000Block082Part012SupportExplicit : Finset ℕ :=
  ([3437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part012 : ℚ :=
  (430007171 : ℚ) / 118613910038400

def SurrogateDiagonalTailChunk000Sub000Block082Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3437
    = surrogateDiagTailX0RatChunk000Sub000Block082Part012

theorem surrogateDiagonalTailChunk000Sub000Block082Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part012] using hcert

def TailChunk000Sub000Block082Part013SupportExplicit : Finset ℕ :=
  ([3439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part013 : ℚ :=
  (28659408187 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block082Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3439
    = surrogateDiagTailX0RatChunk000Sub000Block082Part013

theorem surrogateDiagonalTailChunk000Sub000Block082Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part013] using hcert

def TailChunk000Sub000Block082Part014SupportExplicit : Finset ℕ :=
  ([3441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part014 : ℚ :=
  (1383969529 : ℚ) / 120956538470400

def SurrogateDiagonalTailChunk000Sub000Block082Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3441
    = surrogateDiagTailX0RatChunk000Sub000Block082Part014

theorem surrogateDiagonalTailChunk000Sub000Block082Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part014] using hcert

def TailChunk000Sub000Block082Part015SupportExplicit : Finset ℕ :=
  ([3442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part015 : ℚ :=
  (7401640659 : ℚ) / 291796032870400

def SurrogateDiagonalTailChunk000Sub000Block082Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3442
    = surrogateDiagTailX0RatChunk000Sub000Block082Part015

theorem surrogateDiagonalTailChunk000Sub000Block082Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part015] using hcert

def TailChunk000Sub000Block082Part016SupportExplicit : Finset ℕ :=
  ([3443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part016 : ℚ :=
  (1874374591 : ℚ) / 631849967124480

def SurrogateDiagonalTailChunk000Sub000Block082Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3443
    = surrogateDiagTailX0RatChunk000Sub000Block082Part016

theorem surrogateDiagonalTailChunk000Sub000Block082Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part016] using hcert

def TailChunk000Sub000Block082Part017SupportExplicit : Finset ℕ :=
  ([3445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part017 : ℚ :=
  (203595638075 : ℚ) / 32350718316773376

def SurrogateDiagonalTailChunk000Sub000Block082Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3445
    = surrogateDiagTailX0RatChunk000Sub000Block082Part017

theorem surrogateDiagonalTailChunk000Sub000Block082Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part017] using hcert

def TailChunk000Sub000Block082Part018SupportExplicit : Finset ℕ :=
  ([3446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part018 : ℚ :=
  (1261709825 : ℚ) / 49856393324808

def SurrogateDiagonalTailChunk000Sub000Block082Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3446
    = surrogateDiagTailX0RatChunk000Sub000Block082Part018

theorem surrogateDiagonalTailChunk000Sub000Block082Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part018] using hcert

def TailChunk000Sub000Block082Part019SupportExplicit : Finset ℕ :=
  ([3449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part019 : ℚ :=
  (1486652734975 : ℚ) / 353423877640439808

def SurrogateDiagonalTailChunk000Sub000Block082Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3449
    = surrogateDiagTailX0RatChunk000Sub000Block082Part019

theorem surrogateDiagonalTailChunk000Sub000Block082Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part019] using hcert

def TailChunk000Sub000Block082Part020SupportExplicit : Finset ℕ :=
  ([3451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part020 : ℚ :=
  (119777684975 : ℚ) / 14504454732644352

def SurrogateDiagonalTailChunk000Sub000Block082Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3451
    = surrogateDiagTailX0RatChunk000Sub000Block082Part020

theorem surrogateDiagonalTailChunk000Sub000Block082Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part020] using hcert

def TailChunk000Sub000Block082Part021SupportExplicit : Finset ℕ :=
  ([3453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part021 : ℚ :=
  (16545723947 : ℚ) / 1399484841000000

def SurrogateDiagonalTailChunk000Sub000Block082Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3453
    = surrogateDiagTailX0RatChunk000Sub000Block082Part021

theorem surrogateDiagonalTailChunk000Sub000Block082Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part021] using hcert

def TailChunk000Sub000Block082Part022SupportExplicit : Finset ℕ :=
  ([3454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part022 : ℚ :=
  (3357444821 : ℚ) / 98726557363200

def SurrogateDiagonalTailChunk000Sub000Block082Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3454
    = surrogateDiagTailX0RatChunk000Sub000Block082Part022

theorem surrogateDiagonalTailChunk000Sub000Block082Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part022] using hcert

def TailChunk000Sub000Block082Part023SupportExplicit : Finset ℕ :=
  ([3455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part023 : ℚ :=
  (44095874959 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub000Block082Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3455
    = surrogateDiagTailX0RatChunk000Sub000Block082Part023

theorem surrogateDiagonalTailChunk000Sub000Block082Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part023] using hcert

def TailChunk000Sub000Block082Part024SupportExplicit : Finset ℕ :=
  ([3457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block082Part024 : ℚ :=
  (1493557353775 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub000Block082Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3457
    = surrogateDiagTailX0RatChunk000Sub000Block082Part024

theorem surrogateDiagonalTailChunk000Sub000Block082Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block082Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block082Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block082Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block082Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block082Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block082HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block082Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block082Part000
    + surrogateDiagTailX0RatChunk000Sub000Block082Part001
    + surrogateDiagTailX0RatChunk000Sub000Block082Part002
    + surrogateDiagTailX0RatChunk000Sub000Block082Part003
    + surrogateDiagTailX0RatChunk000Sub000Block082Part004
    + surrogateDiagTailX0RatChunk000Sub000Block082Part005
    + surrogateDiagTailX0RatChunk000Sub000Block082Part006
    + surrogateDiagTailX0RatChunk000Sub000Block082Part007
    + surrogateDiagTailX0RatChunk000Sub000Block082Part008
    + surrogateDiagTailX0RatChunk000Sub000Block082Part009

def surrogateDiagonalTailChunk000Sub000Block082MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block082Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block082Part010
    + surrogateDiagTailX0RatChunk000Sub000Block082Part011
    + surrogateDiagTailX0RatChunk000Sub000Block082Part012
    + surrogateDiagTailX0RatChunk000Sub000Block082Part013
    + surrogateDiagTailX0RatChunk000Sub000Block082Part014
    + surrogateDiagTailX0RatChunk000Sub000Block082Part015
    + surrogateDiagTailX0RatChunk000Sub000Block082Part016
    + surrogateDiagTailX0RatChunk000Sub000Block082Part017
    + surrogateDiagTailX0RatChunk000Sub000Block082Part018
    + surrogateDiagTailX0RatChunk000Sub000Block082Part019

def surrogateDiagonalTailChunk000Sub000Block082TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block082Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block082Part020
    + surrogateDiagTailX0RatChunk000Sub000Block082Part021
    + surrogateDiagTailX0RatChunk000Sub000Block082Part022
    + surrogateDiagTailX0RatChunk000Sub000Block082Part023
    + surrogateDiagTailX0RatChunk000Sub000Block082Part024

def surrogateDiagonalTailChunk000Sub000Block082Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block082HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block082MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block082TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block082 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block082Part000
    + surrogateDiagTailX0RatChunk000Sub000Block082Part001
    + surrogateDiagTailX0RatChunk000Sub000Block082Part002
    + surrogateDiagTailX0RatChunk000Sub000Block082Part003
    + surrogateDiagTailX0RatChunk000Sub000Block082Part004
    + surrogateDiagTailX0RatChunk000Sub000Block082Part005
    + surrogateDiagTailX0RatChunk000Sub000Block082Part006
    + surrogateDiagTailX0RatChunk000Sub000Block082Part007
    + surrogateDiagTailX0RatChunk000Sub000Block082Part008
    + surrogateDiagTailX0RatChunk000Sub000Block082Part009
    + surrogateDiagTailX0RatChunk000Sub000Block082Part010
    + surrogateDiagTailX0RatChunk000Sub000Block082Part011
    + surrogateDiagTailX0RatChunk000Sub000Block082Part012
    + surrogateDiagTailX0RatChunk000Sub000Block082Part013
    + surrogateDiagTailX0RatChunk000Sub000Block082Part014
    + surrogateDiagTailX0RatChunk000Sub000Block082Part015
    + surrogateDiagTailX0RatChunk000Sub000Block082Part016
    + surrogateDiagTailX0RatChunk000Sub000Block082Part017
    + surrogateDiagTailX0RatChunk000Sub000Block082Part018
    + surrogateDiagTailX0RatChunk000Sub000Block082Part019
    + surrogateDiagTailX0RatChunk000Sub000Block082Part020
    + surrogateDiagTailX0RatChunk000Sub000Block082Part021
    + surrogateDiagTailX0RatChunk000Sub000Block082Part022
    + surrogateDiagTailX0RatChunk000Sub000Block082Part023
    + surrogateDiagTailX0RatChunk000Sub000Block082Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block082_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block082Head + surrogateDiagTailX0RatChunk000Sub000Block082Mid + surrogateDiagTailX0RatChunk000Sub000Block082Tail =
      surrogateDiagTailX0RatChunk000Sub000Block082 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block082Head surrogateDiagTailX0RatChunk000Sub000Block082Mid surrogateDiagTailX0RatChunk000Sub000Block082Tail surrogateDiagTailX0RatChunk000Sub000Block082
  ring

def SurrogateDiagonalTailChunk000Sub000Block082HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block082HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block082Head

def SurrogateDiagonalTailChunk000Sub000Block082MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block082MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block082Mid

def SurrogateDiagonalTailChunk000Sub000Block082TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block082TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block082Tail

theorem surrogateDiagonalTailChunk000Sub000Block082_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block082HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block082MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block082TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block082Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block082 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block082HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block082MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block082TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block082Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block082_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
