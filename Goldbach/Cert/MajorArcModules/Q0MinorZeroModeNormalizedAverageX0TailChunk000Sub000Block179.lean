import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [179,180). -/

/-- Block 179 covers tail-support indices [4475,4500) and q from 7414 to 7453. -/

def TailChunk000Sub000Block179Part000SupportExplicit : Finset ℕ :=
  ([7414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part000 : ℚ :=
  (1673638273 : ℚ) / 354112664371200

def SurrogateDiagonalTailChunk000Sub000Block179Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7414
    = surrogateDiagTailX0RatChunk000Sub000Block179Part000

theorem surrogateDiagonalTailChunk000Sub000Block179Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part000] using hcert

def TailChunk000Sub000Block179Part001SupportExplicit : Finset ℕ :=
  ([7415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part001 : ℚ :=
  (2472499129825 : ℚ) / 3087874483711100928

def SurrogateDiagonalTailChunk000Sub000Block179Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7415
    = surrogateDiagTailX0RatChunk000Sub000Block179Part001

theorem surrogateDiagonalTailChunk000Sub000Block179Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part001] using hcert

def TailChunk000Sub000Block179Part002SupportExplicit : Finset ℕ :=
  ([7417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part002 : ℚ :=
  (859560765625 : ℚ) / 1890800689938043392

def SurrogateDiagonalTailChunk000Sub000Block179Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7417
    = surrogateDiagTailX0RatChunk000Sub000Block179Part002

theorem surrogateDiagonalTailChunk000Sub000Block179Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part002] using hcert

def TailChunk000Sub000Block179Part003SupportExplicit : Finset ℕ :=
  ([7418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part003 : ℚ :=
  (1719241207975 : ℚ) / 472700172484510848

def SurrogateDiagonalTailChunk000Sub000Block179Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7418
    = surrogateDiagTailX0RatChunk000Sub000Block179Part003

theorem surrogateDiagonalTailChunk000Sub000Block179Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part003] using hcert

def TailChunk000Sub000Block179Part004SupportExplicit : Finset ℕ :=
  ([7419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part004 : ℚ :=
  (955275207425 : ℚ) / 746982988617498624

def SurrogateDiagonalTailChunk000Sub000Block179Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7419
    = surrogateDiagTailX0RatChunk000Sub000Block179Part004

theorem surrogateDiagonalTailChunk000Sub000Block179Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part004] using hcert

def TailChunk000Sub000Block179Part005SupportExplicit : Finset ℕ :=
  ([7421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part005 : ℚ :=
  (22051136779 : ℚ) / 44798717952000000

def SurrogateDiagonalTailChunk000Sub000Block179Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7421
    = surrogateDiagTailX0RatChunk000Sub000Block179Part005

theorem surrogateDiagonalTailChunk000Sub000Block179Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part005] using hcert

def TailChunk000Sub000Block179Part006SupportExplicit : Finset ℕ :=
  ([7422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part006 : ℚ :=
  (477774539225 : ℚ) / 46686436788593664

def SurrogateDiagonalTailChunk000Sub000Block179Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7422
    = surrogateDiagTailX0RatChunk000Sub000Block179Part006

theorem surrogateDiagonalTailChunk000Sub000Block179Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part006] using hcert

def TailChunk000Sub000Block179Part007SupportExplicit : Finset ℕ :=
  ([7423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part007 : ℚ :=
  (858568633 : ℚ) / 1520368156828800

def SurrogateDiagonalTailChunk000Sub000Block179Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7423
    = surrogateDiagTailX0RatChunk000Sub000Block179Part007

theorem surrogateDiagonalTailChunk000Sub000Block179Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part007] using hcert

def TailChunk000Sub000Block179Part008SupportExplicit : Finset ℕ :=
  ([7426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part008 : ℚ :=
  (1646722531075 : ℚ) / 414416078086128768

def SurrogateDiagonalTailChunk000Sub000Block179Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7426
    = surrogateDiagTailX0RatChunk000Sub000Block179Part008

theorem surrogateDiagonalTailChunk000Sub000Block179Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part008] using hcert

def TailChunk000Sub000Block179Part009SupportExplicit : Finset ℕ :=
  ([7427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part009 : ℚ :=
  (11304236653 : ℚ) / 163649737418803200

def SurrogateDiagonalTailChunk000Sub000Block179Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7427
    = surrogateDiagTailX0RatChunk000Sub000Block179Part009

theorem surrogateDiagonalTailChunk000Sub000Block179Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part009] using hcert

def TailChunk000Sub000Block179Part010SupportExplicit : Finset ℕ :=
  ([7429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part010 : ℚ :=
  (102096852025 : ℚ) / 1343279164488155136

def SurrogateDiagonalTailChunk000Sub000Block179Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7429
    = surrogateDiagTailX0RatChunk000Sub000Block179Part010

theorem surrogateDiagonalTailChunk000Sub000Block179Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part010] using hcert

def TailChunk000Sub000Block179Part011SupportExplicit : Finset ℕ :=
  ([7430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part011 : ℚ :=
  (758399028775 : ℚ) / 194036059033356288

def SurrogateDiagonalTailChunk000Sub000Block179Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7430
    = surrogateDiagTailX0RatChunk000Sub000Block179Part011

theorem surrogateDiagonalTailChunk000Sub000Block179Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part011] using hcert

def TailChunk000Sub000Block179Part012SupportExplicit : Finset ℕ :=
  ([7431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part012 : ℚ :=
  (383396806475 : ℚ) / 751829577683887104

def SurrogateDiagonalTailChunk000Sub000Block179Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7431
    = surrogateDiagTailX0RatChunk000Sub000Block179Part012

theorem surrogateDiagonalTailChunk000Sub000Block179Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part012] using hcert

def TailChunk000Sub000Block179Part013SupportExplicit : Finset ℕ :=
  ([7433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block179Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7433
    = surrogateDiagTailX0RatChunk000Sub000Block179Part013

theorem surrogateDiagonalTailChunk000Sub000Block179Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part013] using hcert

def TailChunk000Sub000Block179Part014SupportExplicit : Finset ℕ :=
  ([7435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part014 : ℚ :=
  (25945088575 : ℚ) / 195084192013235328

def SurrogateDiagonalTailChunk000Sub000Block179Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7435
    = surrogateDiagTailX0RatChunk000Sub000Block179Part014

theorem surrogateDiagonalTailChunk000Sub000Block179Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part014] using hcert

def TailChunk000Sub000Block179Part015SupportExplicit : Finset ℕ :=
  ([7437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part015 : ℚ :=
  (34914471925 : ℚ) / 57957534973476864

def SurrogateDiagonalTailChunk000Sub000Block179Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7437
    = surrogateDiagTailX0RatChunk000Sub000Block179Part015

theorem surrogateDiagonalTailChunk000Sub000Block179Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part015] using hcert

def TailChunk000Sub000Block179Part016SupportExplicit : Finset ℕ :=
  ([7438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part016 : ℚ :=
  (216108765625 : ℚ) / 119455021088582322

def SurrogateDiagonalTailChunk000Sub000Block179Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7438
    = surrogateDiagTailX0RatChunk000Sub000Block179Part016

theorem surrogateDiagonalTailChunk000Sub000Block179Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part016] using hcert

def TailChunk000Sub000Block179Part017SupportExplicit : Finset ℕ :=
  ([7439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part017 : ℚ :=
  (66518649625 : ℚ) / 6809854112240191488

def SurrogateDiagonalTailChunk000Sub000Block179Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7439
    = surrogateDiagTailX0RatChunk000Sub000Block179Part017

theorem surrogateDiagonalTailChunk000Sub000Block179Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part017] using hcert

def TailChunk000Sub000Block179Part018SupportExplicit : Finset ℕ :=
  ([7441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part018 : ℚ :=
  (354043523275 : ℚ) / 4122208243001881728

def SurrogateDiagonalTailChunk000Sub000Block179Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7441
    = surrogateDiagTailX0RatChunk000Sub000Block179Part018

theorem surrogateDiagonalTailChunk000Sub000Block179Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part018] using hcert

def TailChunk000Sub000Block179Part019SupportExplicit : Finset ℕ :=
  ([7445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part019 : ℚ :=
  (277226843675 : ℚ) / 1569092524629295104

def SurrogateDiagonalTailChunk000Sub000Block179Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7445
    = surrogateDiagTailX0RatChunk000Sub000Block179Part019

theorem surrogateDiagonalTailChunk000Sub000Block179Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part019] using hcert

def TailChunk000Sub000Block179Part020SupportExplicit : Finset ℕ :=
  ([7446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part020 : ℚ :=
  (210581258725 : ℚ) / 23487430237618176

def SurrogateDiagonalTailChunk000Sub000Block179Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7446
    = surrogateDiagTailX0RatChunk000Sub000Block179Part020

theorem surrogateDiagonalTailChunk000Sub000Block179Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part020] using hcert

def TailChunk000Sub000Block179Part021SupportExplicit : Finset ℕ :=
  ([7447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part021 : ℚ :=
  (2704184637 : ℚ) / 69622943329638400

def SurrogateDiagonalTailChunk000Sub000Block179Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7447
    = surrogateDiagTailX0RatChunk000Sub000Block179Part021

theorem surrogateDiagonalTailChunk000Sub000Block179Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part021] using hcert

def TailChunk000Sub000Block179Part022SupportExplicit : Finset ℕ :=
  ([7449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part022 : ℚ :=
  (30886773397 : ℚ) / 43246027572019200

def SurrogateDiagonalTailChunk000Sub000Block179Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7449
    = surrogateDiagTailX0RatChunk000Sub000Block179Part022

theorem surrogateDiagonalTailChunk000Sub000Block179Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part022] using hcert

def TailChunk000Sub000Block179Part023SupportExplicit : Finset ℕ :=
  ([7451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block179Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7451
    = surrogateDiagTailX0RatChunk000Sub000Block179Part023

theorem surrogateDiagonalTailChunk000Sub000Block179Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part023] using hcert

def TailChunk000Sub000Block179Part024SupportExplicit : Finset ℕ :=
  ([7453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block179Part024 : ℚ :=
  (86273474275 : ℚ) / 6601138509434585088

def SurrogateDiagonalTailChunk000Sub000Block179Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7453
    = surrogateDiagTailX0RatChunk000Sub000Block179Part024

theorem surrogateDiagonalTailChunk000Sub000Block179Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block179Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block179Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block179Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block179Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block179Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block179HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block179Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part000
    + surrogateDiagTailX0RatChunk000Sub000Block179Part001
    + surrogateDiagTailX0RatChunk000Sub000Block179Part002
    + surrogateDiagTailX0RatChunk000Sub000Block179Part003
    + surrogateDiagTailX0RatChunk000Sub000Block179Part004
    + surrogateDiagTailX0RatChunk000Sub000Block179Part005
    + surrogateDiagTailX0RatChunk000Sub000Block179Part006
    + surrogateDiagTailX0RatChunk000Sub000Block179Part007
    + surrogateDiagTailX0RatChunk000Sub000Block179Part008
    + surrogateDiagTailX0RatChunk000Sub000Block179Part009

def surrogateDiagonalTailChunk000Sub000Block179MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block179Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part010
    + surrogateDiagTailX0RatChunk000Sub000Block179Part011
    + surrogateDiagTailX0RatChunk000Sub000Block179Part012
    + surrogateDiagTailX0RatChunk000Sub000Block179Part013
    + surrogateDiagTailX0RatChunk000Sub000Block179Part014
    + surrogateDiagTailX0RatChunk000Sub000Block179Part015
    + surrogateDiagTailX0RatChunk000Sub000Block179Part016
    + surrogateDiagTailX0RatChunk000Sub000Block179Part017
    + surrogateDiagTailX0RatChunk000Sub000Block179Part018
    + surrogateDiagTailX0RatChunk000Sub000Block179Part019

def surrogateDiagonalTailChunk000Sub000Block179TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block179Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part020
    + surrogateDiagTailX0RatChunk000Sub000Block179Part021
    + surrogateDiagTailX0RatChunk000Sub000Block179Part022
    + surrogateDiagTailX0RatChunk000Sub000Block179Part023
    + surrogateDiagTailX0RatChunk000Sub000Block179Part024

def surrogateDiagonalTailChunk000Sub000Block179Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block179HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block179MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block179TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block179 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block179Part000
    + surrogateDiagTailX0RatChunk000Sub000Block179Part001
    + surrogateDiagTailX0RatChunk000Sub000Block179Part002
    + surrogateDiagTailX0RatChunk000Sub000Block179Part003
    + surrogateDiagTailX0RatChunk000Sub000Block179Part004
    + surrogateDiagTailX0RatChunk000Sub000Block179Part005
    + surrogateDiagTailX0RatChunk000Sub000Block179Part006
    + surrogateDiagTailX0RatChunk000Sub000Block179Part007
    + surrogateDiagTailX0RatChunk000Sub000Block179Part008
    + surrogateDiagTailX0RatChunk000Sub000Block179Part009
    + surrogateDiagTailX0RatChunk000Sub000Block179Part010
    + surrogateDiagTailX0RatChunk000Sub000Block179Part011
    + surrogateDiagTailX0RatChunk000Sub000Block179Part012
    + surrogateDiagTailX0RatChunk000Sub000Block179Part013
    + surrogateDiagTailX0RatChunk000Sub000Block179Part014
    + surrogateDiagTailX0RatChunk000Sub000Block179Part015
    + surrogateDiagTailX0RatChunk000Sub000Block179Part016
    + surrogateDiagTailX0RatChunk000Sub000Block179Part017
    + surrogateDiagTailX0RatChunk000Sub000Block179Part018
    + surrogateDiagTailX0RatChunk000Sub000Block179Part019
    + surrogateDiagTailX0RatChunk000Sub000Block179Part020
    + surrogateDiagTailX0RatChunk000Sub000Block179Part021
    + surrogateDiagTailX0RatChunk000Sub000Block179Part022
    + surrogateDiagTailX0RatChunk000Sub000Block179Part023
    + surrogateDiagTailX0RatChunk000Sub000Block179Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block179_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block179Head + surrogateDiagTailX0RatChunk000Sub000Block179Mid + surrogateDiagTailX0RatChunk000Sub000Block179Tail =
      surrogateDiagTailX0RatChunk000Sub000Block179 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block179Head surrogateDiagTailX0RatChunk000Sub000Block179Mid surrogateDiagTailX0RatChunk000Sub000Block179Tail surrogateDiagTailX0RatChunk000Sub000Block179
  ring

def SurrogateDiagonalTailChunk000Sub000Block179HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block179HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block179Head

def SurrogateDiagonalTailChunk000Sub000Block179MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block179MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block179Mid

def SurrogateDiagonalTailChunk000Sub000Block179TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block179TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block179Tail

theorem surrogateDiagonalTailChunk000Sub000Block179_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block179HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block179MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block179TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block179Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block179 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block179HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block179MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block179TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block179Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block179_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
