import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [156,157). -/

/- Block 156 covers tail-support indices [3900,3925) and q from 6467 to 6505. -/

def TailChunk000Sub000Block156Part000SupportExplicit : Finset ℕ :=
  ([6467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part000 : ℚ :=
  (622186859425 : ℚ) / 933277704146145792

def SurrogateDiagonalTailChunk000Sub000Block156Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6467
    = surrogateDiagTailX0RatChunk000Sub000Block156Part000

theorem surrogateDiagonalTailChunk000Sub000Block156Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part000] using hcert

def TailChunk000Sub000Block156Part001SupportExplicit : Finset ℕ :=
  ([6469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part001 : ℚ :=
  (653874390625 : ℚ) / 1094074541829495072

def SurrogateDiagonalTailChunk000Sub000Block156Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6469
    = surrogateDiagTailX0RatChunk000Sub000Block156Part001

theorem surrogateDiagonalTailChunk000Sub000Block156Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part001] using hcert

def TailChunk000Sub000Block156Part002SupportExplicit : Finset ℕ :=
  ([6470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part002 : ℚ :=
  (330850599525 : ℚ) / 37159994535417856

def SurrogateDiagonalTailChunk000Sub000Block156Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6470
    = surrogateDiagTailX0RatChunk000Sub000Block156Part002

theorem surrogateDiagonalTailChunk000Sub000Block156Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part002] using hcert

def TailChunk000Sub000Block156Part003SupportExplicit : Finset ℕ :=
  ([6473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part003 : ℚ :=
  (654683265625 : ℚ) / 1096783483998392832

def SurrogateDiagonalTailChunk000Sub000Block156Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6473
    = surrogateDiagTailX0RatChunk000Sub000Block156Part003

theorem surrogateDiagonalTailChunk000Sub000Block156Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part003] using hcert

def TailChunk000Sub000Block156Part004SupportExplicit : Finset ℕ :=
  ([6474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part004 : ℚ :=
  (59917030775 : ℚ) / 3125690618241024

def SurrogateDiagonalTailChunk000Sub000Block156Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6474
    = surrogateDiagTailX0RatChunk000Sub000Block156Part004

theorem surrogateDiagonalTailChunk000Sub000Block156Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part004] using hcert

def TailChunk000Sub000Block156Part005SupportExplicit : Finset ℕ :=
  ([6477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part005 : ℚ :=
  (593288241475 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub000Block156Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6477
    = surrogateDiagTailX0RatChunk000Sub000Block156Part005

theorem surrogateDiagonalTailChunk000Sub000Block156Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part005] using hcert

def TailChunk000Sub000Block156Part006SupportExplicit : Finset ℕ :=
  ([6478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part006 : ℚ :=
  (6444676363 : ℚ) / 2369437376716800

def SurrogateDiagonalTailChunk000Sub000Block156Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6478
    = surrogateDiagTailX0RatChunk000Sub000Block156Part006

theorem surrogateDiagonalTailChunk000Sub000Block156Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part006] using hcert

def TailChunk000Sub000Block156Part007SupportExplicit : Finset ℕ :=
  ([6479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part007 : ℚ :=
  (6127962947 : ℚ) / 42523783056000000

def SurrogateDiagonalTailChunk000Sub000Block156Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6479
    = surrogateDiagTailX0RatChunk000Sub000Block156Part007

theorem surrogateDiagonalTailChunk000Sub000Block156Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part007] using hcert

def TailChunk000Sub000Block156Part008SupportExplicit : Finset ℕ :=
  ([6481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block156Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6481
    = surrogateDiagTailX0RatChunk000Sub000Block156Part008

theorem surrogateDiagonalTailChunk000Sub000Block156Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part008] using hcert

def TailChunk000Sub000Block156Part009SupportExplicit : Finset ℕ :=
  ([6482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part009 : ℚ :=
  (153900858025 : ℚ) / 36909636771424032

def SurrogateDiagonalTailChunk000Sub000Block156Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6482
    = surrogateDiagTailX0RatChunk000Sub000Block156Part009

theorem surrogateDiagonalTailChunk000Sub000Block156Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part009] using hcert

def TailChunk000Sub000Block156Part010SupportExplicit : Finset ℕ :=
  ([6483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part010 : ℚ :=
  (11674165379 : ℚ) / 17417741539737600

def SurrogateDiagonalTailChunk000Sub000Block156Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6483
    = surrogateDiagTailX0RatChunk000Sub000Block156Part010

theorem surrogateDiagonalTailChunk000Sub000Block156Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part010] using hcert

def TailChunk000Sub000Block156Part011SupportExplicit : Finset ℕ :=
  ([6485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part011 : ℚ :=
  (210451010075 : ℚ) / 902935721419997184

def SurrogateDiagonalTailChunk000Sub000Block156Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6485
    = surrogateDiagTailX0RatChunk000Sub000Block156Part011

theorem surrogateDiagonalTailChunk000Sub000Block156Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part011] using hcert

def TailChunk000Sub000Block156Part012SupportExplicit : Finset ℕ :=
  ([6486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part012 : ℚ :=
  (552416141275 : ℚ) / 41963228276901888

def SurrogateDiagonalTailChunk000Sub000Block156Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6486
    = surrogateDiagTailX0RatChunk000Sub000Block156Part012

theorem surrogateDiagonalTailChunk000Sub000Block156Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part012] using hcert

def TailChunk000Sub000Block156Part013SupportExplicit : Finset ℕ :=
  ([6487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part013 : ℚ :=
  (1909341875 : ℚ) / 38422986812430336

def SurrogateDiagonalTailChunk000Sub000Block156Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6487
    = surrogateDiagTailX0RatChunk000Sub000Block156Part013

theorem surrogateDiagonalTailChunk000Sub000Block156Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part013] using hcert

def TailChunk000Sub000Block156Part014SupportExplicit : Finset ℕ :=
  ([6490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part014 : ℚ :=
  (22505530459 : ℚ) / 2897602380595200

def SurrogateDiagonalTailChunk000Sub000Block156Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6490
    = surrogateDiagTailX0RatChunk000Sub000Block156Part014

theorem surrogateDiagonalTailChunk000Sub000Block156Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part014] using hcert

def TailChunk000Sub000Block156Part015SupportExplicit : Finset ℕ :=
  ([6491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block156Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6491
    = surrogateDiagTailX0RatChunk000Sub000Block156Part015

theorem surrogateDiagonalTailChunk000Sub000Block156Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part015] using hcert

def TailChunk000Sub000Block156Part016SupportExplicit : Finset ℕ :=
  ([6493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part016 : ℚ :=
  (17572291 : ℚ) / 1167119377200000

def SurrogateDiagonalTailChunk000Sub000Block156Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6493
    = surrogateDiagTailX0RatChunk000Sub000Block156Part016

theorem surrogateDiagonalTailChunk000Sub000Block156Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part016] using hcert

def TailChunk000Sub000Block156Part017SupportExplicit : Finset ℕ :=
  ([6494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part017 : ℚ :=
  (48581130037 : ℚ) / 8542425199411200

def SurrogateDiagonalTailChunk000Sub000Block156Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6494
    = surrogateDiagTailX0RatChunk000Sub000Block156Part017

theorem surrogateDiagonalTailChunk000Sub000Block156Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part017] using hcert

def TailChunk000Sub000Block156Part018SupportExplicit : Finset ℕ :=
  ([6495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part018 : ℚ :=
  (666227718275 : ℚ) / 178357673366913024

def SurrogateDiagonalTailChunk000Sub000Block156Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6495
    = surrogateDiagTailX0RatChunk000Sub000Block156Part018

theorem surrogateDiagonalTailChunk000Sub000Block156Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part018] using hcert

def TailChunk000Sub000Block156Part019SupportExplicit : Finset ℕ :=
  ([6497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part019 : ℚ :=
  (426442960925 : ℚ) / 671639582244077568

def SurrogateDiagonalTailChunk000Sub000Block156Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6497
    = surrogateDiagTailX0RatChunk000Sub000Block156Part019

theorem surrogateDiagonalTailChunk000Sub000Block156Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part019] using hcert

def TailChunk000Sub000Block156Part020SupportExplicit : Finset ℕ :=
  ([6499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part020 : ℚ :=
  (284374374125 : ℚ) / 447759721496051712

def SurrogateDiagonalTailChunk000Sub000Block156Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6499
    = surrogateDiagTailX0RatChunk000Sub000Block156Part020

theorem surrogateDiagonalTailChunk000Sub000Block156Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part020] using hcert

def TailChunk000Sub000Block156Part021SupportExplicit : Finset ℕ :=
  ([6501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part021 : ℚ :=
  (1033582887 : ℚ) / 393622457016320

def SurrogateDiagonalTailChunk000Sub000Block156Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6501
    = surrogateDiagTailX0RatChunk000Sub000Block156Part021

theorem surrogateDiagonalTailChunk000Sub000Block156Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part021] using hcert

def TailChunk000Sub000Block156Part022SupportExplicit : Finset ℕ :=
  ([6502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part022 : ℚ :=
  (52834435999 : ℚ) / 11158871953125000

def SurrogateDiagonalTailChunk000Sub000Block156Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6502
    = surrogateDiagTailX0RatChunk000Sub000Block156Part022

theorem surrogateDiagonalTailChunk000Sub000Block156Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part022] using hcert

def TailChunk000Sub000Block156Part023SupportExplicit : Finset ℕ :=
  ([6503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part023 : ℚ :=
  (2155219612375 : ℚ) / 2403387318560882688

def SurrogateDiagonalTailChunk000Sub000Block156Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6503
    = surrogateDiagTailX0RatChunk000Sub000Block156Part023

theorem surrogateDiagonalTailChunk000Sub000Block156Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part023] using hcert

def TailChunk000Sub000Block156Part024SupportExplicit : Finset ℕ :=
  ([6505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block156Part024 : ℚ :=
  (40170108197 : ℚ) / 36565391616000000

def SurrogateDiagonalTailChunk000Sub000Block156Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6505
    = surrogateDiagTailX0RatChunk000Sub000Block156Part024

theorem surrogateDiagonalTailChunk000Sub000Block156Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block156Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block156Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block156Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block156Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block156Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block156Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block156HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block156Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block156Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block156Part000
    + surrogateDiagTailX0RatChunk000Sub000Block156Part001
    + surrogateDiagTailX0RatChunk000Sub000Block156Part002
    + surrogateDiagTailX0RatChunk000Sub000Block156Part003
    + surrogateDiagTailX0RatChunk000Sub000Block156Part004
    + surrogateDiagTailX0RatChunk000Sub000Block156Part005
    + surrogateDiagTailX0RatChunk000Sub000Block156Part006
    + surrogateDiagTailX0RatChunk000Sub000Block156Part007
    + surrogateDiagTailX0RatChunk000Sub000Block156Part008
    + surrogateDiagTailX0RatChunk000Sub000Block156Part009

def surrogateDiagonalTailChunk000Sub000Block156MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block156Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block156Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block156Part010
    + surrogateDiagTailX0RatChunk000Sub000Block156Part011
    + surrogateDiagTailX0RatChunk000Sub000Block156Part012
    + surrogateDiagTailX0RatChunk000Sub000Block156Part013
    + surrogateDiagTailX0RatChunk000Sub000Block156Part014
    + surrogateDiagTailX0RatChunk000Sub000Block156Part015
    + surrogateDiagTailX0RatChunk000Sub000Block156Part016
    + surrogateDiagTailX0RatChunk000Sub000Block156Part017
    + surrogateDiagTailX0RatChunk000Sub000Block156Part018
    + surrogateDiagTailX0RatChunk000Sub000Block156Part019

def surrogateDiagonalTailChunk000Sub000Block156TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block156Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block156Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block156Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block156Part020
    + surrogateDiagTailX0RatChunk000Sub000Block156Part021
    + surrogateDiagTailX0RatChunk000Sub000Block156Part022
    + surrogateDiagTailX0RatChunk000Sub000Block156Part023
    + surrogateDiagTailX0RatChunk000Sub000Block156Part024

def surrogateDiagonalTailChunk000Sub000Block156Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block156HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block156MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block156TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block156 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block156Part000
    + surrogateDiagTailX0RatChunk000Sub000Block156Part001
    + surrogateDiagTailX0RatChunk000Sub000Block156Part002
    + surrogateDiagTailX0RatChunk000Sub000Block156Part003
    + surrogateDiagTailX0RatChunk000Sub000Block156Part004
    + surrogateDiagTailX0RatChunk000Sub000Block156Part005
    + surrogateDiagTailX0RatChunk000Sub000Block156Part006
    + surrogateDiagTailX0RatChunk000Sub000Block156Part007
    + surrogateDiagTailX0RatChunk000Sub000Block156Part008
    + surrogateDiagTailX0RatChunk000Sub000Block156Part009
    + surrogateDiagTailX0RatChunk000Sub000Block156Part010
    + surrogateDiagTailX0RatChunk000Sub000Block156Part011
    + surrogateDiagTailX0RatChunk000Sub000Block156Part012
    + surrogateDiagTailX0RatChunk000Sub000Block156Part013
    + surrogateDiagTailX0RatChunk000Sub000Block156Part014
    + surrogateDiagTailX0RatChunk000Sub000Block156Part015
    + surrogateDiagTailX0RatChunk000Sub000Block156Part016
    + surrogateDiagTailX0RatChunk000Sub000Block156Part017
    + surrogateDiagTailX0RatChunk000Sub000Block156Part018
    + surrogateDiagTailX0RatChunk000Sub000Block156Part019
    + surrogateDiagTailX0RatChunk000Sub000Block156Part020
    + surrogateDiagTailX0RatChunk000Sub000Block156Part021
    + surrogateDiagTailX0RatChunk000Sub000Block156Part022
    + surrogateDiagTailX0RatChunk000Sub000Block156Part023
    + surrogateDiagTailX0RatChunk000Sub000Block156Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block156_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block156Head + surrogateDiagTailX0RatChunk000Sub000Block156Mid + surrogateDiagTailX0RatChunk000Sub000Block156Tail =
      surrogateDiagTailX0RatChunk000Sub000Block156 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block156Head surrogateDiagTailX0RatChunk000Sub000Block156Mid surrogateDiagTailX0RatChunk000Sub000Block156Tail surrogateDiagTailX0RatChunk000Sub000Block156
  ring

def SurrogateDiagonalTailChunk000Sub000Block156HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block156HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block156Head

def SurrogateDiagonalTailChunk000Sub000Block156MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block156MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block156Mid

def SurrogateDiagonalTailChunk000Sub000Block156TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block156TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block156Tail

theorem surrogateDiagonalTailChunk000Sub000Block156_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block156HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block156MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block156TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block156Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block156 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block156HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block156MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block156TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block156Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block156_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
