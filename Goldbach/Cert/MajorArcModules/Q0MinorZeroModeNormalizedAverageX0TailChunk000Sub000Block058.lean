import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [58,59). -/

/- Block 058 covers tail-support indices [1450,1475) and q from 2435 to 2473. -/

def TailChunk000Sub000Block058Part000SupportExplicit : Finset ℕ :=
  ([2435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part000 : ℚ :=
  (147964211875 : ℚ) / 8927953300173312

def SurrogateDiagonalTailChunk000Sub000Block058Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2435
    = surrogateDiagTailX0RatChunk000Sub000Block058Part000

theorem surrogateDiagonalTailChunk000Sub000Block058Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part000] using hcert

def TailChunk000Sub000Block058Part001SupportExplicit : Finset ℕ :=
  ([2437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part001 : ℚ :=
  (742222650775 : ℚ) / 88051345090708608

def SurrogateDiagonalTailChunk000Sub000Block058Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2437
    = surrogateDiagTailX0RatChunk000Sub000Block058Part001

theorem surrogateDiagonalTailChunk000Sub000Block058Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part001] using hcert

def TailChunk000Sub000Block058Part002SupportExplicit : Finset ℕ :=
  ([2438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part002 : ℚ :=
  (87342286225 : ℚ) / 1070707797299712

def SurrogateDiagonalTailChunk000Sub000Block058Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2438
    = surrogateDiagTailX0RatChunk000Sub000Block058Part002

theorem surrogateDiagonalTailChunk000Sub000Block058Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part002] using hcert

def TailChunk000Sub000Block058Part003SupportExplicit : Finset ℕ :=
  ([2441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part003 : ℚ :=
  (29786446519 : ℚ) / 3545244203059200

def SurrogateDiagonalTailChunk000Sub000Block058Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2441
    = surrogateDiagTailX0RatChunk000Sub000Block058Part003

theorem surrogateDiagonalTailChunk000Sub000Block058Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part003] using hcert

def TailChunk000Sub000Block058Part004SupportExplicit : Finset ℕ :=
  ([2442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part004 : ℚ :=
  (440933291 : ℚ) / 1343961538560

def SurrogateDiagonalTailChunk000Sub000Block058Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2442
    = surrogateDiagTailX0RatChunk000Sub000Block058Part004

theorem surrogateDiagonalTailChunk000Sub000Block058Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part004] using hcert

def TailChunk000Sub000Block058Part005SupportExplicit : Finset ℕ :=
  ([2443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part005 : ℚ :=
  (70865857825 : ℚ) / 5280880338634752

def SurrogateDiagonalTailChunk000Sub000Block058Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2443
    = surrogateDiagTailX0RatChunk000Sub000Block058Part005

theorem surrogateDiagonalTailChunk000Sub000Block058Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part005] using hcert

def TailChunk000Sub000Block058Part006SupportExplicit : Finset ℕ :=
  ([2445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part006 : ℚ :=
  (198932247725 : ℚ) / 3527092661796864

def SurrogateDiagonalTailChunk000Sub000Block058Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2445
    = surrogateDiagTailX0RatChunk000Sub000Block058Part006

theorem surrogateDiagonalTailChunk000Sub000Block058Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part006] using hcert

def TailChunk000Sub000Block058Part007SupportExplicit : Finset ℕ :=
  ([2446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part007 : ℚ :=
  (186853945325 : ℚ) / 2787928855096164

def SurrogateDiagonalTailChunk000Sub000Block058Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2446
    = surrogateDiagTailX0RatChunk000Sub000Block058Part007

theorem surrogateDiagonalTailChunk000Sub000Block058Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part007] using hcert

def TailChunk000Sub000Block058Part008SupportExplicit : Finset ℕ :=
  ([2447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part008 : ℚ :=
  (748326429775 : ℚ) / 89506107299571528

def SurrogateDiagonalTailChunk000Sub000Block058Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2447
    = surrogateDiagTailX0RatChunk000Sub000Block058Part008

theorem surrogateDiagonalTailChunk000Sub000Block058Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part008] using hcert

def TailChunk000Sub000Block058Part009SupportExplicit : Finset ℕ :=
  ([2449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part009 : ℚ :=
  (3186804469 : ℚ) / 333202131100800

def SurrogateDiagonalTailChunk000Sub000Block058Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2449
    = surrogateDiagTailX0RatChunk000Sub000Block058Part009

theorem surrogateDiagonalTailChunk000Sub000Block058Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part009] using hcert

def TailChunk000Sub000Block058Part010SupportExplicit : Finset ℕ :=
  ([2451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part010 : ℚ :=
  (303292754525 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block058Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2451
    = surrogateDiagTailX0RatChunk000Sub000Block058Part010

theorem surrogateDiagonalTailChunk000Sub000Block058Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part010] using hcert

def TailChunk000Sub000Block058Part011SupportExplicit : Finset ℕ :=
  ([2453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part011 : ℚ :=
  (5447242229 : ℚ) / 485879687706240

def SurrogateDiagonalTailChunk000Sub000Block058Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2453
    = surrogateDiagTailX0RatChunk000Sub000Block058Part011

theorem surrogateDiagonalTailChunk000Sub000Block058Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part011] using hcert

def TailChunk000Sub000Block058Part012SupportExplicit : Finset ℕ :=
  ([2454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part012 : ℚ :=
  (16687975 : ℚ) / 73894035456

def SurrogateDiagonalTailChunk000Sub000Block058Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2454
    = surrogateDiagTailX0RatChunk000Sub000Block058Part012

theorem surrogateDiagonalTailChunk000Sub000Block058Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part012] using hcert

def TailChunk000Sub000Block058Part013SupportExplicit : Finset ℕ :=
  ([2455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part013 : ℚ :=
  (1203237599 : ℚ) / 73804210690560

def SurrogateDiagonalTailChunk000Sub000Block058Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2455
    = surrogateDiagTailX0RatChunk000Sub000Block058Part013

theorem surrogateDiagonalTailChunk000Sub000Block058Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part013] using hcert

def TailChunk000Sub000Block058Part014SupportExplicit : Finset ℕ :=
  ([2458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part014 : ℚ :=
  (188691841925 : ℚ) / 2843088184256064

def SurrogateDiagonalTailChunk000Sub000Block058Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2458
    = surrogateDiagTailX0RatChunk000Sub000Block058Part014

theorem surrogateDiagonalTailChunk000Sub000Block058Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part014] using hcert

def TailChunk000Sub000Block058Part015SupportExplicit : Finset ℕ :=
  ([2459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part015 : ℚ :=
  (755683957975 : ℚ) / 91275532035355848

def SurrogateDiagonalTailChunk000Sub000Block058Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2459
    = surrogateDiagTailX0RatChunk000Sub000Block058Part015

theorem surrogateDiagonalTailChunk000Sub000Block058Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part015] using hcert

def TailChunk000Sub000Block058Part016SupportExplicit : Finset ℕ :=
  ([2461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part016 : ℚ :=
  (718322705725 : ℚ) / 73950487825577088

def SurrogateDiagonalTailChunk000Sub000Block058Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2461
    = surrogateDiagTailX0RatChunk000Sub000Block058Part016

theorem surrogateDiagonalTailChunk000Sub000Block058Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part016] using hcert

def TailChunk000Sub000Block058Part017SupportExplicit : Finset ℕ :=
  ([2462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part017 : ℚ :=
  (7572258917 : ℚ) / 114466209164100

def SurrogateDiagonalTailChunk000Sub000Block058Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2462
    = surrogateDiagTailX0RatChunk000Sub000Block058Part017

theorem surrogateDiagonalTailChunk000Sub000Block058Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part017] using hcert

def TailChunk000Sub000Block058Part018SupportExplicit : Finset ℕ :=
  ([2463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part018 : ℚ :=
  (807879 : ℚ) / 28935792640

def SurrogateDiagonalTailChunk000Sub000Block058Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2463
    = surrogateDiagTailX0RatChunk000Sub000Block058Part018

theorem surrogateDiagonalTailChunk000Sub000Block058Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part018] using hcert

def TailChunk000Sub000Block058Part019SupportExplicit : Finset ℕ :=
  ([2465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part019 : ℚ :=
  (184229892675 : ℚ) / 8595232434159616

def SurrogateDiagonalTailChunk000Sub000Block058Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2465
    = surrogateDiagTailX0RatChunk000Sub000Block058Part019

theorem surrogateDiagonalTailChunk000Sub000Block058Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part019] using hcert

def TailChunk000Sub000Block058Part020SupportExplicit : Finset ℕ :=
  ([2467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part020 : ℚ :=
  (760608972775 : ℚ) / 92469635969988168

def SurrogateDiagonalTailChunk000Sub000Block058Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2467
    = surrogateDiagTailX0RatChunk000Sub000Block058Part020

theorem surrogateDiagonalTailChunk000Sub000Block058Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part020] using hcert

def TailChunk000Sub000Block058Part021SupportExplicit : Finset ℕ :=
  ([2469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part021 : ℚ :=
  (3758425 : ℚ) / 135273738624

def SurrogateDiagonalTailChunk000Sub000Block058Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2469
    = surrogateDiagTailX0RatChunk000Sub000Block058Part021

theorem surrogateDiagonalTailChunk000Sub000Block058Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part021] using hcert

def TailChunk000Sub000Block058Part022SupportExplicit : Finset ℕ :=
  ([2470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part022 : ℚ :=
  (133534334525 : ℚ) / 696709661589504

def SurrogateDiagonalTailChunk000Sub000Block058Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2470
    = surrogateDiagTailX0RatChunk000Sub000Block058Part022

theorem surrogateDiagonalTailChunk000Sub000Block058Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part022] using hcert

def TailChunk000Sub000Block058Part023SupportExplicit : Finset ℕ :=
  ([2471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part023 : ℚ :=
  (72499517825 : ℚ) / 5527897796247552

def SurrogateDiagonalTailChunk000Sub000Block058Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2471
    = surrogateDiagTailX0RatChunk000Sub000Block058Part023

theorem surrogateDiagonalTailChunk000Sub000Block058Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part023] using hcert

def TailChunk000Sub000Block058Part024SupportExplicit : Finset ℕ :=
  ([2473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block058Part024 : ℚ :=
  (764313231775 : ℚ) / 93372873577187328

def SurrogateDiagonalTailChunk000Sub000Block058Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2473
    = surrogateDiagTailX0RatChunk000Sub000Block058Part024

theorem surrogateDiagonalTailChunk000Sub000Block058Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block058Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block058Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block058Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block058Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block058Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block058HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block058Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block058Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block058Part000
    + surrogateDiagTailX0RatChunk000Sub000Block058Part001
    + surrogateDiagTailX0RatChunk000Sub000Block058Part002
    + surrogateDiagTailX0RatChunk000Sub000Block058Part003
    + surrogateDiagTailX0RatChunk000Sub000Block058Part004
    + surrogateDiagTailX0RatChunk000Sub000Block058Part005
    + surrogateDiagTailX0RatChunk000Sub000Block058Part006
    + surrogateDiagTailX0RatChunk000Sub000Block058Part007
    + surrogateDiagTailX0RatChunk000Sub000Block058Part008
    + surrogateDiagTailX0RatChunk000Sub000Block058Part009

def surrogateDiagonalTailChunk000Sub000Block058MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block058Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block058Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block058Part010
    + surrogateDiagTailX0RatChunk000Sub000Block058Part011
    + surrogateDiagTailX0RatChunk000Sub000Block058Part012
    + surrogateDiagTailX0RatChunk000Sub000Block058Part013
    + surrogateDiagTailX0RatChunk000Sub000Block058Part014
    + surrogateDiagTailX0RatChunk000Sub000Block058Part015
    + surrogateDiagTailX0RatChunk000Sub000Block058Part016
    + surrogateDiagTailX0RatChunk000Sub000Block058Part017
    + surrogateDiagTailX0RatChunk000Sub000Block058Part018
    + surrogateDiagTailX0RatChunk000Sub000Block058Part019

def surrogateDiagonalTailChunk000Sub000Block058TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block058Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block058Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block058Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block058Part020
    + surrogateDiagTailX0RatChunk000Sub000Block058Part021
    + surrogateDiagTailX0RatChunk000Sub000Block058Part022
    + surrogateDiagTailX0RatChunk000Sub000Block058Part023
    + surrogateDiagTailX0RatChunk000Sub000Block058Part024

def surrogateDiagonalTailChunk000Sub000Block058Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block058HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block058MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block058TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block058 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block058Part000
    + surrogateDiagTailX0RatChunk000Sub000Block058Part001
    + surrogateDiagTailX0RatChunk000Sub000Block058Part002
    + surrogateDiagTailX0RatChunk000Sub000Block058Part003
    + surrogateDiagTailX0RatChunk000Sub000Block058Part004
    + surrogateDiagTailX0RatChunk000Sub000Block058Part005
    + surrogateDiagTailX0RatChunk000Sub000Block058Part006
    + surrogateDiagTailX0RatChunk000Sub000Block058Part007
    + surrogateDiagTailX0RatChunk000Sub000Block058Part008
    + surrogateDiagTailX0RatChunk000Sub000Block058Part009
    + surrogateDiagTailX0RatChunk000Sub000Block058Part010
    + surrogateDiagTailX0RatChunk000Sub000Block058Part011
    + surrogateDiagTailX0RatChunk000Sub000Block058Part012
    + surrogateDiagTailX0RatChunk000Sub000Block058Part013
    + surrogateDiagTailX0RatChunk000Sub000Block058Part014
    + surrogateDiagTailX0RatChunk000Sub000Block058Part015
    + surrogateDiagTailX0RatChunk000Sub000Block058Part016
    + surrogateDiagTailX0RatChunk000Sub000Block058Part017
    + surrogateDiagTailX0RatChunk000Sub000Block058Part018
    + surrogateDiagTailX0RatChunk000Sub000Block058Part019
    + surrogateDiagTailX0RatChunk000Sub000Block058Part020
    + surrogateDiagTailX0RatChunk000Sub000Block058Part021
    + surrogateDiagTailX0RatChunk000Sub000Block058Part022
    + surrogateDiagTailX0RatChunk000Sub000Block058Part023
    + surrogateDiagTailX0RatChunk000Sub000Block058Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block058_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block058Head + surrogateDiagTailX0RatChunk000Sub000Block058Mid + surrogateDiagTailX0RatChunk000Sub000Block058Tail =
      surrogateDiagTailX0RatChunk000Sub000Block058 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block058Head surrogateDiagTailX0RatChunk000Sub000Block058Mid surrogateDiagTailX0RatChunk000Sub000Block058Tail surrogateDiagTailX0RatChunk000Sub000Block058
  ring

def SurrogateDiagonalTailChunk000Sub000Block058HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block058HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block058Head

def SurrogateDiagonalTailChunk000Sub000Block058MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block058MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block058Mid

def SurrogateDiagonalTailChunk000Sub000Block058TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block058TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block058Tail

theorem surrogateDiagonalTailChunk000Sub000Block058_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block058HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block058MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block058TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block058Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block058 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block058HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block058MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block058TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block058Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block058_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
