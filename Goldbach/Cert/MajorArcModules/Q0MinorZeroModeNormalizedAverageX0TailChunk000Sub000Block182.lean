import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [182,183). -/

/-- Block 182 covers tail-support indices [4550,4575) and q from 7535 to 7574. -/

def TailChunk000Sub000Block182Part000SupportExplicit : Finset ℕ :=
  ([7535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part000 : ℚ :=
  (94750856503 : ℚ) / 87595631719219200

def SurrogateDiagonalTailChunk000Sub000Block182Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7535
    = surrogateDiagTailX0RatChunk000Sub000Block182Part000

theorem surrogateDiagonalTailChunk000Sub000Block182Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part000] using hcert

def TailChunk000Sub000Block182Part001SupportExplicit : Finset ℕ :=
  ([7537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part001 : ℚ :=
  (887599515625 : ℚ) / 2016185219762429952

def SurrogateDiagonalTailChunk000Sub000Block182Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7537
    = surrogateDiagTailX0RatChunk000Sub000Block182Part001

theorem surrogateDiagonalTailChunk000Sub000Block182Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part001] using hcert

def TailChunk000Sub000Block182Part002SupportExplicit : Finset ℕ :=
  ([7538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part002 : ℚ :=
  (221958765625 : ℚ) / 126011576235151872

def SurrogateDiagonalTailChunk000Sub000Block182Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7538
    = surrogateDiagTailX0RatChunk000Sub000Block182Part002

theorem surrogateDiagonalTailChunk000Sub000Block182Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part002] using hcert

def TailChunk000Sub000Block182Part003SupportExplicit : Finset ℕ :=
  ([7539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part003 : ℚ :=
  (28616645725 : ℚ) / 31544248508504064

def SurrogateDiagonalTailChunk000Sub000Block182Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7539
    = surrogateDiagTailX0RatChunk000Sub000Block182Part003

theorem surrogateDiagonalTailChunk000Sub000Block182Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part003] using hcert

def TailChunk000Sub000Block182Part004SupportExplicit : Finset ℕ :=
  ([7541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7541
    = surrogateDiagTailX0RatChunk000Sub000Block182Part004

theorem surrogateDiagonalTailChunk000Sub000Block182Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part004] using hcert

def TailChunk000Sub000Block182Part005SupportExplicit : Finset ℕ :=
  ([7543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part005 : ℚ :=
  (204827525 : ℚ) / 9961451323566336

def SurrogateDiagonalTailChunk000Sub000Block182Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7543
    = surrogateDiagTailX0RatChunk000Sub000Block182Part005

theorem surrogateDiagonalTailChunk000Sub000Block182Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part005] using hcert

def TailChunk000Sub000Block182Part006SupportExplicit : Finset ℕ :=
  ([7545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part006 : ℚ :=
  (758345821825 : ℚ) / 650431664324640768

def SurrogateDiagonalTailChunk000Sub000Block182Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7545
    = surrogateDiagTailX0RatChunk000Sub000Block182Part006

theorem surrogateDiagonalTailChunk000Sub000Block182Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part006] using hcert

def TailChunk000Sub000Block182Part007SupportExplicit : Finset ℕ :=
  ([7547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7547
    = surrogateDiagTailX0RatChunk000Sub000Block182Part007

theorem surrogateDiagonalTailChunk000Sub000Block182Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part007] using hcert

def TailChunk000Sub000Block182Part008SupportExplicit : Finset ℕ :=
  ([7549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7549
    = surrogateDiagTailX0RatChunk000Sub000Block182Part008

theorem surrogateDiagonalTailChunk000Sub000Block182Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part008] using hcert

def TailChunk000Sub000Block182Part009SupportExplicit : Finset ℕ :=
  ([7553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part009 : ℚ :=
  (480221934775 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk000Sub000Block182Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7553
    = surrogateDiagTailX0RatChunk000Sub000Block182Part009

theorem surrogateDiagonalTailChunk000Sub000Block182Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part009] using hcert

def TailChunk000Sub000Block182Part010SupportExplicit : Finset ℕ :=
  ([7554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part010 : ℚ :=
  (693115223275 : ℚ) / 100200388634352768

def SurrogateDiagonalTailChunk000Sub000Block182Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7554
    = surrogateDiagTailX0RatChunk000Sub000Block182Part010

theorem surrogateDiagonalTailChunk000Sub000Block182Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part010] using hcert

def TailChunk000Sub000Block182Part011SupportExplicit : Finset ℕ :=
  ([7555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part011 : ℚ :=
  (3806218509 : ℚ) / 22186221999795200

def SurrogateDiagonalTailChunk000Sub000Block182Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7555
    = surrogateDiagTailX0RatChunk000Sub000Block182Part011

theorem surrogateDiagonalTailChunk000Sub000Block182Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part011] using hcert

def TailChunk000Sub000Block182Part012SupportExplicit : Finset ℕ :=
  ([7557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part012 : ℚ :=
  (1681649263 : ℚ) / 2276106714316800

def SurrogateDiagonalTailChunk000Sub000Block182Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7557
    = surrogateDiagTailX0RatChunk000Sub000Block182Part012

theorem surrogateDiagonalTailChunk000Sub000Block182Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part012] using hcert

def TailChunk000Sub000Block182Part013SupportExplicit : Finset ℕ :=
  ([7558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part013 : ℚ :=
  (223138140625 : ℚ) / 127354613419928082

def SurrogateDiagonalTailChunk000Sub000Block182Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7558
    = surrogateDiagTailX0RatChunk000Sub000Block182Part013

theorem surrogateDiagonalTailChunk000Sub000Block182Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part013] using hcert

def TailChunk000Sub000Block182Part014SupportExplicit : Finset ℕ :=
  ([7559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7559
    = surrogateDiagTailX0RatChunk000Sub000Block182Part014

theorem surrogateDiagonalTailChunk000Sub000Block182Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part014] using hcert

def TailChunk000Sub000Block182Part015SupportExplicit : Finset ℕ :=
  ([7561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7561
    = surrogateDiagTailX0RatChunk000Sub000Block182Part015

theorem surrogateDiagonalTailChunk000Sub000Block182Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part015] using hcert

def TailChunk000Sub000Block182Part016SupportExplicit : Finset ℕ :=
  ([7562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part016 : ℚ :=
  (858441081175 : ℚ) / 403438778604436608

def SurrogateDiagonalTailChunk000Sub000Block182Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7562
    = surrogateDiagTailX0RatChunk000Sub000Block182Part016

theorem surrogateDiagonalTailChunk000Sub000Block182Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part016] using hcert

def TailChunk000Sub000Block182Part017SupportExplicit : Finset ℕ :=
  ([7563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part017 : ℚ :=
  (15885322259 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block182Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7563
    = surrogateDiagTailX0RatChunk000Sub000Block182Part017

theorem surrogateDiagonalTailChunk000Sub000Block182Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part017] using hcert

def TailChunk000Sub000Block182Part018SupportExplicit : Finset ℕ :=
  ([7565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part018 : ℚ :=
  (165849338025 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub000Block182Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7565
    = surrogateDiagTailX0RatChunk000Sub000Block182Part018

theorem surrogateDiagonalTailChunk000Sub000Block182Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part018] using hcert

def TailChunk000Sub000Block182Part019SupportExplicit : Finset ℕ :=
  ([7566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part019 : ℚ :=
  (160861292275 : ℚ) / 17615572678213632

def SurrogateDiagonalTailChunk000Sub000Block182Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7566
    = surrogateDiagTailX0RatChunk000Sub000Block182Part019

theorem surrogateDiagonalTailChunk000Sub000Block182Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part019] using hcert

def TailChunk000Sub000Block182Part020SupportExplicit : Finset ℕ :=
  ([7567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part020 : ℚ :=
  (49283466425 : ℚ) / 377669054492116992

def SurrogateDiagonalTailChunk000Sub000Block182Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7567
    = surrogateDiagTailX0RatChunk000Sub000Block182Part020

theorem surrogateDiagonalTailChunk000Sub000Block182Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part020] using hcert

def TailChunk000Sub000Block182Part021SupportExplicit : Finset ℕ :=
  ([7570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part021 : ℚ :=
  (262413414425 : ℚ) / 69699995728183296

def SurrogateDiagonalTailChunk000Sub000Block182Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7570
    = surrogateDiagTailX0RatChunk000Sub000Block182Part021

theorem surrogateDiagonalTailChunk000Sub000Block182Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part021] using hcert

def TailChunk000Sub000Block182Part022SupportExplicit : Finset ℕ :=
  ([7571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part022 : ℚ :=
  (441974125 : ℚ) / 59252154503528448

def SurrogateDiagonalTailChunk000Sub000Block182Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7571
    = surrogateDiagTailX0RatChunk000Sub000Block182Part022

theorem surrogateDiagonalTailChunk000Sub000Block182Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part022] using hcert

def TailChunk000Sub000Block182Part023SupportExplicit : Finset ℕ :=
  ([7573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block182Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7573
    = surrogateDiagTailX0RatChunk000Sub000Block182Part023

theorem surrogateDiagonalTailChunk000Sub000Block182Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part023] using hcert

def TailChunk000Sub000Block182Part024SupportExplicit : Finset ℕ :=
  ([7574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block182Part024 : ℚ :=
  (32156715553 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub000Block182Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7574
    = surrogateDiagTailX0RatChunk000Sub000Block182Part024

theorem surrogateDiagonalTailChunk000Sub000Block182Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block182Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block182Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block182Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block182Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block182Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block182HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block182Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block182Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part000
    + surrogateDiagTailX0RatChunk000Sub000Block182Part001
    + surrogateDiagTailX0RatChunk000Sub000Block182Part002
    + surrogateDiagTailX0RatChunk000Sub000Block182Part003
    + surrogateDiagTailX0RatChunk000Sub000Block182Part004
    + surrogateDiagTailX0RatChunk000Sub000Block182Part005
    + surrogateDiagTailX0RatChunk000Sub000Block182Part006
    + surrogateDiagTailX0RatChunk000Sub000Block182Part007
    + surrogateDiagTailX0RatChunk000Sub000Block182Part008
    + surrogateDiagTailX0RatChunk000Sub000Block182Part009

def surrogateDiagonalTailChunk000Sub000Block182MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block182Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block182Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part010
    + surrogateDiagTailX0RatChunk000Sub000Block182Part011
    + surrogateDiagTailX0RatChunk000Sub000Block182Part012
    + surrogateDiagTailX0RatChunk000Sub000Block182Part013
    + surrogateDiagTailX0RatChunk000Sub000Block182Part014
    + surrogateDiagTailX0RatChunk000Sub000Block182Part015
    + surrogateDiagTailX0RatChunk000Sub000Block182Part016
    + surrogateDiagTailX0RatChunk000Sub000Block182Part017
    + surrogateDiagTailX0RatChunk000Sub000Block182Part018
    + surrogateDiagTailX0RatChunk000Sub000Block182Part019

def surrogateDiagonalTailChunk000Sub000Block182TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block182Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block182Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block182Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part020
    + surrogateDiagTailX0RatChunk000Sub000Block182Part021
    + surrogateDiagTailX0RatChunk000Sub000Block182Part022
    + surrogateDiagTailX0RatChunk000Sub000Block182Part023
    + surrogateDiagTailX0RatChunk000Sub000Block182Part024

def surrogateDiagonalTailChunk000Sub000Block182Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block182HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block182MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block182TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block182 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block182Part000
    + surrogateDiagTailX0RatChunk000Sub000Block182Part001
    + surrogateDiagTailX0RatChunk000Sub000Block182Part002
    + surrogateDiagTailX0RatChunk000Sub000Block182Part003
    + surrogateDiagTailX0RatChunk000Sub000Block182Part004
    + surrogateDiagTailX0RatChunk000Sub000Block182Part005
    + surrogateDiagTailX0RatChunk000Sub000Block182Part006
    + surrogateDiagTailX0RatChunk000Sub000Block182Part007
    + surrogateDiagTailX0RatChunk000Sub000Block182Part008
    + surrogateDiagTailX0RatChunk000Sub000Block182Part009
    + surrogateDiagTailX0RatChunk000Sub000Block182Part010
    + surrogateDiagTailX0RatChunk000Sub000Block182Part011
    + surrogateDiagTailX0RatChunk000Sub000Block182Part012
    + surrogateDiagTailX0RatChunk000Sub000Block182Part013
    + surrogateDiagTailX0RatChunk000Sub000Block182Part014
    + surrogateDiagTailX0RatChunk000Sub000Block182Part015
    + surrogateDiagTailX0RatChunk000Sub000Block182Part016
    + surrogateDiagTailX0RatChunk000Sub000Block182Part017
    + surrogateDiagTailX0RatChunk000Sub000Block182Part018
    + surrogateDiagTailX0RatChunk000Sub000Block182Part019
    + surrogateDiagTailX0RatChunk000Sub000Block182Part020
    + surrogateDiagTailX0RatChunk000Sub000Block182Part021
    + surrogateDiagTailX0RatChunk000Sub000Block182Part022
    + surrogateDiagTailX0RatChunk000Sub000Block182Part023
    + surrogateDiagTailX0RatChunk000Sub000Block182Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block182_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block182Head + surrogateDiagTailX0RatChunk000Sub000Block182Mid + surrogateDiagTailX0RatChunk000Sub000Block182Tail =
      surrogateDiagTailX0RatChunk000Sub000Block182 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block182Head surrogateDiagTailX0RatChunk000Sub000Block182Mid surrogateDiagTailX0RatChunk000Sub000Block182Tail surrogateDiagTailX0RatChunk000Sub000Block182
  ring

def SurrogateDiagonalTailChunk000Sub000Block182HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block182HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block182Head

def SurrogateDiagonalTailChunk000Sub000Block182MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block182MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block182Mid

def SurrogateDiagonalTailChunk000Sub000Block182TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block182TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block182Tail

theorem surrogateDiagonalTailChunk000Sub000Block182_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block182HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block182MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block182TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block182Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block182 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block182HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block182MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block182TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block182Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block182_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
