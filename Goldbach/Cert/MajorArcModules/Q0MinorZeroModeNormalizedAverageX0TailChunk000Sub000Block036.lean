import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [36,37). -/

/- Block 036 covers tail-support indices [900,925) and q from 1527 to 1565. -/

def TailChunk000Sub000Block036Part000SupportExplicit : Finset ℕ :=
  ([1527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part000 : ℚ :=
  (307133113975 : ℚ) / 2664413900064768

def SurrogateDiagonalTailChunk000Sub000Block036Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1527
    = surrogateDiagTailX0RatChunk000Sub000Block036Part000

theorem surrogateDiagonalTailChunk000Sub000Block036Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part000] using hcert

def TailChunk000Sub000Block036Part001SupportExplicit : Finset ℕ :=
  ([1529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part001 : ℚ :=
  (7990759781 : ℚ) / 181373235393600

def SurrogateDiagonalTailChunk000Sub000Block036Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1529
    = surrogateDiagTailX0RatChunk000Sub000Block036Part001

theorem surrogateDiagonalTailChunk000Sub000Block036Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part001] using hcert

def TailChunk000Sub000Block036Part002SupportExplicit : Finset ℕ :=
  ([1531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part002 : ℚ :=
  (114854089 : ℚ) / 3582293315400

def SurrogateDiagonalTailChunk000Sub000Block036Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1531
    = surrogateDiagTailX0RatChunk000Sub000Block036Part002

theorem surrogateDiagonalTailChunk000Sub000Block036Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part002] using hcert

def TailChunk000Sub000Block036Part003SupportExplicit : Finset ℕ :=
  ([1533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part003 : ℚ :=
  (262625787175 : ℚ) / 1393419323179008

def SurrogateDiagonalTailChunk000Sub000Block036Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1533
    = surrogateDiagTailX0RatChunk000Sub000Block036Part003

theorem surrogateDiagonalTailChunk000Sub000Block036Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part003] using hcert

def TailChunk000Sub000Block036Part004SupportExplicit : Finset ℕ :=
  ([1534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part004 : ℚ :=
  (232061997175 : ℚ) / 586764482070528

def SurrogateDiagonalTailChunk000Sub000Block036Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1534
    = surrogateDiagTailX0RatChunk000Sub000Block036Part004

theorem surrogateDiagonalTailChunk000Sub000Block036Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part004] using hcert

def TailChunk000Sub000Block036Part005SupportExplicit : Finset ℕ :=
  ([1535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part005 : ℚ :=
  (21076757375 : ℚ) / 330144151947264

def SurrogateDiagonalTailChunk000Sub000Block036Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1535
    = surrogateDiagTailX0RatChunk000Sub000Block036Part005

theorem surrogateDiagonalTailChunk000Sub000Block036Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part005] using hcert

def TailChunk000Sub000Block036Part006SupportExplicit : Finset ℕ :=
  ([1537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part006 : ℚ :=
  (1098164775 : ℚ) / 29264501756672

def SurrogateDiagonalTailChunk000Sub000Block036Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1537
    = surrogateDiagTailX0RatChunk000Sub000Block036Part006

theorem surrogateDiagonalTailChunk000Sub000Block036Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part006] using hcert

def TailChunk000Sub000Block036Part007SupportExplicit : Finset ℕ :=
  ([1538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part007 : ℚ :=
  (2735044625 : ℚ) / 10739565723648

def SurrogateDiagonalTailChunk000Sub000Block036Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1538
    = surrogateDiagTailX0RatChunk000Sub000Block036Part007

theorem surrogateDiagonalTailChunk000Sub000Block036Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part007] using hcert

def TailChunk000Sub000Block036Part008SupportExplicit : Finset ℕ :=
  ([1541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part008 : ℚ :=
  (52719926825 : ℚ) / 1389323357989776

def SurrogateDiagonalTailChunk000Sub000Block036Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1541
    = surrogateDiagTailX0RatChunk000Sub000Block036Part008

theorem surrogateDiagonalTailChunk000Sub000Block036Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part008] using hcert

def TailChunk000Sub000Block036Part009SupportExplicit : Finset ℕ :=
  ([1542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part009 : ℚ :=
  (76102210925 : ℚ) / 85916525789184

def SurrogateDiagonalTailChunk000Sub000Block036Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1542
    = surrogateDiagTailX0RatChunk000Sub000Block036Part009

theorem surrogateDiagonalTailChunk000Sub000Block036Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part009] using hcert

def TailChunk000Sub000Block036Part010SupportExplicit : Finset ℕ :=
  ([1543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part010 : ℚ :=
  (49581180425 : ℚ) / 1570803442228872

def SurrogateDiagonalTailChunk000Sub000Block036Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1543
    = surrogateDiagTailX0RatChunk000Sub000Block036Part010

theorem surrogateDiagonalTailChunk000Sub000Block036Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part010] using hcert

def TailChunk000Sub000Block036Part011SupportExplicit : Finset ℕ :=
  ([1545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part011 : ℚ :=
  (31283552375 : ℚ) / 138579026743296

def SurrogateDiagonalTailChunk000Sub000Block036Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1545
    = surrogateDiagTailX0RatChunk000Sub000Block036Part011

theorem surrogateDiagonalTailChunk000Sub000Block036Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part011] using hcert

def TailChunk000Sub000Block036Part012SupportExplicit : Finset ℕ :=
  ([1546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part012 : ℚ :=
  (261105234775 : ℚ) / 888169919104128

def SurrogateDiagonalTailChunk000Sub000Block036Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1546
    = surrogateDiagTailX0RatChunk000Sub000Block036Part012

theorem surrogateDiagonalTailChunk000Sub000Block036Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part012] using hcert

def TailChunk000Sub000Block036Part013SupportExplicit : Finset ℕ :=
  ([1547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part013 : ℚ :=
  (171209903975 : ℚ) / 2201946584776704

def SurrogateDiagonalTailChunk000Sub000Block036Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1547
    = surrogateDiagTailX0RatChunk000Sub000Block036Part013

theorem surrogateDiagonalTailChunk000Sub000Block036Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part013] using hcert

def TailChunk000Sub000Block036Part014SupportExplicit : Finset ℕ :=
  ([1549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part014 : ℚ :=
  (299745169925 : ℚ) / 7179276643735104

def SurrogateDiagonalTailChunk000Sub000Block036Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1549
    = surrogateDiagTailX0RatChunk000Sub000Block036Part014

theorem surrogateDiagonalTailChunk000Sub000Block036Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part014] using hcert

def TailChunk000Sub000Block036Part015SupportExplicit : Finset ℕ :=
  ([1551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part015 : ℚ :=
  (719374803 : ℚ) / 4776908257280

def SurrogateDiagonalTailChunk000Sub000Block036Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1551
    = surrogateDiagTailX0RatChunk000Sub000Block036Part015

theorem surrogateDiagonalTailChunk000Sub000Block036Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part015] using hcert

def TailChunk000Sub000Block036Part016SupportExplicit : Finset ℕ :=
  ([1553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part016 : ℚ :=
  (301295239325 : ℚ) / 7253769163259904

def SurrogateDiagonalTailChunk000Sub000Block036Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1553
    = surrogateDiagTailX0RatChunk000Sub000Block036Part016

theorem surrogateDiagonalTailChunk000Sub000Block036Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part016] using hcert

def TailChunk000Sub000Block036Part017SupportExplicit : Finset ℕ :=
  ([1554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part017 : ℚ :=
  (2038145425 : ℚ) / 1360761057792

def SurrogateDiagonalTailChunk000Sub000Block036Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1554
    = surrogateDiagTailX0RatChunk000Sub000Block036Part017

theorem surrogateDiagonalTailChunk000Sub000Block036Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part017] using hcert

def TailChunk000Sub000Block036Part018SupportExplicit : Finset ℕ :=
  ([1555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part018 : ℚ :=
  (980535261 : ℚ) / 15764577351680

def SurrogateDiagonalTailChunk000Sub000Block036Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1555
    = surrogateDiagTailX0RatChunk000Sub000Block036Part018

theorem surrogateDiagonalTailChunk000Sub000Block036Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part018] using hcert

def TailChunk000Sub000Block036Part019SupportExplicit : Finset ℕ :=
  ([1558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part019 : ℚ :=
  (9752764171 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block036Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1558
    = surrogateDiagTailX0RatChunk000Sub000Block036Part019

theorem surrogateDiagonalTailChunk000Sub000Block036Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part019] using hcert

def TailChunk000Sub000Block036Part020SupportExplicit : Finset ℕ :=
  ([1559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part020 : ℚ :=
  (151844300475 : ℚ) / 4911062006411416

def SurrogateDiagonalTailChunk000Sub000Block036Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1559
    = surrogateDiagTailX0RatChunk000Sub000Block036Part020

theorem surrogateDiagonalTailChunk000Sub000Block036Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part020] using hcert

def TailChunk000Sub000Block036Part021SupportExplicit : Finset ℕ :=
  ([1561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part021 : ℚ :=
  (196568128325 : ℚ) / 3935625470420544

def SurrogateDiagonalTailChunk000Sub000Block036Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1561
    = surrogateDiagTailX0RatChunk000Sub000Block036Part021

theorem surrogateDiagonalTailChunk000Sub000Block036Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part021] using hcert

def TailChunk000Sub000Block036Part022SupportExplicit : Finset ℕ :=
  ([1562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part022 : ℚ :=
  (2753021673 : ℚ) / 8004934000000

def SurrogateDiagonalTailChunk000Sub000Block036Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1562
    = surrogateDiagTailX0RatChunk000Sub000Block036Part022

theorem surrogateDiagonalTailChunk000Sub000Block036Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part022] using hcert

def TailChunk000Sub000Block036Part023SupportExplicit : Finset ℕ :=
  ([1563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part023 : ℚ :=
  (3724846627 : ℚ) / 29252313292800

def SurrogateDiagonalTailChunk000Sub000Block036Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1563
    = surrogateDiagTailX0RatChunk000Sub000Block036Part023

theorem surrogateDiagonalTailChunk000Sub000Block036Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part023] using hcert

def TailChunk000Sub000Block036Part024SupportExplicit : Finset ℕ :=
  ([1565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block036Part024 : ℚ :=
  (372444405625 : ℚ) / 6065759684395008

def SurrogateDiagonalTailChunk000Sub000Block036Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1565
    = surrogateDiagTailX0RatChunk000Sub000Block036Part024

theorem surrogateDiagonalTailChunk000Sub000Block036Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block036Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block036Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block036Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block036Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block036Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block036HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block036Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block036Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block036Part000
    + surrogateDiagTailX0RatChunk000Sub000Block036Part001
    + surrogateDiagTailX0RatChunk000Sub000Block036Part002
    + surrogateDiagTailX0RatChunk000Sub000Block036Part003
    + surrogateDiagTailX0RatChunk000Sub000Block036Part004
    + surrogateDiagTailX0RatChunk000Sub000Block036Part005
    + surrogateDiagTailX0RatChunk000Sub000Block036Part006
    + surrogateDiagTailX0RatChunk000Sub000Block036Part007
    + surrogateDiagTailX0RatChunk000Sub000Block036Part008
    + surrogateDiagTailX0RatChunk000Sub000Block036Part009

def surrogateDiagonalTailChunk000Sub000Block036MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block036Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block036Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block036Part010
    + surrogateDiagTailX0RatChunk000Sub000Block036Part011
    + surrogateDiagTailX0RatChunk000Sub000Block036Part012
    + surrogateDiagTailX0RatChunk000Sub000Block036Part013
    + surrogateDiagTailX0RatChunk000Sub000Block036Part014
    + surrogateDiagTailX0RatChunk000Sub000Block036Part015
    + surrogateDiagTailX0RatChunk000Sub000Block036Part016
    + surrogateDiagTailX0RatChunk000Sub000Block036Part017
    + surrogateDiagTailX0RatChunk000Sub000Block036Part018
    + surrogateDiagTailX0RatChunk000Sub000Block036Part019

def surrogateDiagonalTailChunk000Sub000Block036TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block036Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block036Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block036Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block036Part020
    + surrogateDiagTailX0RatChunk000Sub000Block036Part021
    + surrogateDiagTailX0RatChunk000Sub000Block036Part022
    + surrogateDiagTailX0RatChunk000Sub000Block036Part023
    + surrogateDiagTailX0RatChunk000Sub000Block036Part024

def surrogateDiagonalTailChunk000Sub000Block036Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block036HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block036MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block036TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block036 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block036Part000
    + surrogateDiagTailX0RatChunk000Sub000Block036Part001
    + surrogateDiagTailX0RatChunk000Sub000Block036Part002
    + surrogateDiagTailX0RatChunk000Sub000Block036Part003
    + surrogateDiagTailX0RatChunk000Sub000Block036Part004
    + surrogateDiagTailX0RatChunk000Sub000Block036Part005
    + surrogateDiagTailX0RatChunk000Sub000Block036Part006
    + surrogateDiagTailX0RatChunk000Sub000Block036Part007
    + surrogateDiagTailX0RatChunk000Sub000Block036Part008
    + surrogateDiagTailX0RatChunk000Sub000Block036Part009
    + surrogateDiagTailX0RatChunk000Sub000Block036Part010
    + surrogateDiagTailX0RatChunk000Sub000Block036Part011
    + surrogateDiagTailX0RatChunk000Sub000Block036Part012
    + surrogateDiagTailX0RatChunk000Sub000Block036Part013
    + surrogateDiagTailX0RatChunk000Sub000Block036Part014
    + surrogateDiagTailX0RatChunk000Sub000Block036Part015
    + surrogateDiagTailX0RatChunk000Sub000Block036Part016
    + surrogateDiagTailX0RatChunk000Sub000Block036Part017
    + surrogateDiagTailX0RatChunk000Sub000Block036Part018
    + surrogateDiagTailX0RatChunk000Sub000Block036Part019
    + surrogateDiagTailX0RatChunk000Sub000Block036Part020
    + surrogateDiagTailX0RatChunk000Sub000Block036Part021
    + surrogateDiagTailX0RatChunk000Sub000Block036Part022
    + surrogateDiagTailX0RatChunk000Sub000Block036Part023
    + surrogateDiagTailX0RatChunk000Sub000Block036Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block036_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block036Head + surrogateDiagTailX0RatChunk000Sub000Block036Mid + surrogateDiagTailX0RatChunk000Sub000Block036Tail =
      surrogateDiagTailX0RatChunk000Sub000Block036 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block036Head surrogateDiagTailX0RatChunk000Sub000Block036Mid surrogateDiagTailX0RatChunk000Sub000Block036Tail surrogateDiagTailX0RatChunk000Sub000Block036
  ring

def SurrogateDiagonalTailChunk000Sub000Block036HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block036HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block036Head

def SurrogateDiagonalTailChunk000Sub000Block036MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block036MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block036Mid

def SurrogateDiagonalTailChunk000Sub000Block036TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block036TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block036Tail

theorem surrogateDiagonalTailChunk000Sub000Block036_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block036HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block036MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block036TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block036Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block036 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block036HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block036MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block036TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block036Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block036_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
