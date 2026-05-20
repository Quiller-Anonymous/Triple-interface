import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [35,36). -/

/- Block 035 covers tail-support indices [875,900) and q from 1487 to 1526. -/

def TailChunk000Sub000Block035Part000SupportExplicit : Finset ℕ :=
  ([1487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part000 : ℚ :=
  (138142783275 : ℚ) / 4064254000275736

def SurrogateDiagonalTailChunk000Sub000Block035Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1487
    = surrogateDiagTailX0RatChunk000Sub000Block035Part000

theorem surrogateDiagonalTailChunk000Sub000Block035Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part000] using hcert

def TailChunk000Sub000Block035Part001SupportExplicit : Finset ℕ :=
  ([1489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part001 : ℚ :=
  (276973840925 : ℚ) / 6129267674333184

def SurrogateDiagonalTailChunk000Sub000Block035Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1489
    = surrogateDiagTailX0RatChunk000Sub000Block035Part001

theorem surrogateDiagonalTailChunk000Sub000Block035Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part001] using hcert

def TailChunk000Sub000Block035Part002SupportExplicit : Finset ℕ :=
  ([1490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part002 : ℚ :=
  (770400675 : ℚ) / 1383441219584

def SurrogateDiagonalTailChunk000Sub000Block035Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1490
    = surrogateDiagTailX0RatChunk000Sub000Block035Part002

theorem surrogateDiagonalTailChunk000Sub000Block035Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part002] using hcert

def TailChunk000Sub000Block035Part003SupportExplicit : Finset ℕ :=
  ([1491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part003 : ℚ :=
  (370327913 : ℚ) / 1844336793600

def SurrogateDiagonalTailChunk000Sub000Block035Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1491
    = surrogateDiagTailX0RatChunk000Sub000Block035Part003

theorem surrogateDiagonalTailChunk000Sub000Block035Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part003] using hcert

def TailChunk000Sub000Block035Part004SupportExplicit : Finset ℕ :=
  ([1493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part004 : ℚ :=
  (278463946325 : ℚ) / 6195440005353024

def SurrogateDiagonalTailChunk000Sub000Block035Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1493
    = surrogateDiagTailX0RatChunk000Sub000Block035Part004

theorem surrogateDiagonalTailChunk000Sub000Block035Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part004] using hcert

def TailChunk000Sub000Block035Part005SupportExplicit : Finset ℕ :=
  ([1495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part005 : ℚ :=
  (152437028375 : ℚ) / 1554721255194624

def SurrogateDiagonalTailChunk000Sub000Block035Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1495
    = surrogateDiagTailX0RatChunk000Sub000Block035Part005

theorem surrogateDiagonalTailChunk000Sub000Block035Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part005] using hcert

def TailChunk000Sub000Block035Part006SupportExplicit : Finset ℕ :=
  ([1497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part006 : ℚ :=
  (295184600725 : ℚ) / 2460731408512128

def SurrogateDiagonalTailChunk000Sub000Block035Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1497
    = surrogateDiagTailX0RatChunk000Sub000Block035Part006

theorem surrogateDiagonalTailChunk000Sub000Block035Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part006] using hcert

def TailChunk000Sub000Block035Part007SupportExplicit : Finset ℕ :=
  ([1498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part007 : ℚ :=
  (206953981525 : ℚ) / 409124343547008

def SurrogateDiagonalTailChunk000Sub000Block035Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1498
    = surrogateDiagTailX0RatChunk000Sub000Block035Part007

theorem surrogateDiagonalTailChunk000Sub000Block035Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part007] using hcert

def TailChunk000Sub000Block035Part008SupportExplicit : Finset ℕ :=
  ([1499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part008 : ℚ :=
  (2864926275 : ℚ) / 85655800387864

def SurrogateDiagonalTailChunk000Sub000Block035Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1499
    = surrogateDiagTailX0RatChunk000Sub000Block035Part008

theorem surrogateDiagonalTailChunk000Sub000Block035Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part008] using hcert

def TailChunk000Sub000Block035Part009SupportExplicit : Finset ℕ :=
  ([1501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part009 : ℚ :=
  (398052208825 : ℚ) / 9716174142899328

def SurrogateDiagonalTailChunk000Sub000Block035Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1501
    = surrogateDiagTailX0RatChunk000Sub000Block035Part009

theorem surrogateDiagonalTailChunk000Sub000Block035Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part009] using hcert

def TailChunk000Sub000Block035Part010SupportExplicit : Finset ℕ :=
  ([1502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part010 : ℚ :=
  (9858173479 : ℚ) / 31646953125000

def SurrogateDiagonalTailChunk000Sub000Block035Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1502
    = surrogateDiagTailX0RatChunk000Sub000Block035Part010

theorem surrogateDiagonalTailChunk000Sub000Block035Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part010] using hcert

def TailChunk000Sub000Block035Part011SupportExplicit : Finset ℕ :=
  ([1505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part011 : ℚ :=
  (146860069175 : ℚ) / 1290740661633024

def SurrogateDiagonalTailChunk000Sub000Block035Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1505
    = surrogateDiagTailX0RatChunk000Sub000Block035Part011

theorem surrogateDiagonalTailChunk000Sub000Block035Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part011] using hcert

def TailChunk000Sub000Block035Part012SupportExplicit : Finset ℕ :=
  ([1506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part012 : ℚ :=
  (725911529 : ℚ) / 781406250000

def SurrogateDiagonalTailChunk000Sub000Block035Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1506
    = surrogateDiagTailX0RatChunk000Sub000Block035Part012

theorem surrogateDiagonalTailChunk000Sub000Block035Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part012] using hcert

def TailChunk000Sub000Block035Part013SupportExplicit : Finset ℕ :=
  ([1507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part013 : ℚ :=
  (10074762839 : ℚ) / 171085218201600

def SurrogateDiagonalTailChunk000Sub000Block035Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1507
    = surrogateDiagTailX0RatChunk000Sub000Block035Part013

theorem surrogateDiagonalTailChunk000Sub000Block035Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part013] using hcert

def TailChunk000Sub000Block035Part014SupportExplicit : Finset ℕ :=
  ([1509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part014 : ℚ :=
  (14206425 : ℚ) / 127012032032

def SurrogateDiagonalTailChunk000Sub000Block035Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1509
    = surrogateDiagTailX0RatChunk000Sub000Block035Part014

theorem surrogateDiagonalTailChunk000Sub000Block035Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part014] using hcert

def TailChunk000Sub000Block035Part015SupportExplicit : Finset ℕ :=
  ([1510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part015 : ℚ :=
  (1742442943 : ℚ) / 3240648000000

def SurrogateDiagonalTailChunk000Sub000Block035Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1510
    = surrogateDiagTailX0RatChunk000Sub000Block035Part015

theorem surrogateDiagonalTailChunk000Sub000Block035Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part015] using hcert

def TailChunk000Sub000Block035Part016SupportExplicit : Finset ℕ :=
  ([1511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part016 : ℚ :=
  (11408755637 : ℚ) / 259994789060100

def SurrogateDiagonalTailChunk000Sub000Block035Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1511
    = surrogateDiagTailX0RatChunk000Sub000Block035Part016

theorem surrogateDiagonalTailChunk000Sub000Block035Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part016] using hcert

def TailChunk000Sub000Block035Part017SupportExplicit : Finset ℕ :=
  ([1513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part017 : ℚ :=
  (67145307825 : ℚ) / 1637895643332608

def SurrogateDiagonalTailChunk000Sub000Block035Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1513
    = surrogateDiagTailX0RatChunk000Sub000Block035Part017

theorem surrogateDiagonalTailChunk000Sub000Block035Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part017] using hcert

def TailChunk000Sub000Block035Part018SupportExplicit : Finset ℕ :=
  ([1514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part018 : ℚ :=
  (35772583825 : ℚ) / 116685260705664

def SurrogateDiagonalTailChunk000Sub000Block035Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1514
    = surrogateDiagTailX0RatChunk000Sub000Block035Part018

theorem surrogateDiagonalTailChunk000Sub000Block035Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part018] using hcert

def TailChunk000Sub000Block035Part019SupportExplicit : Finset ℕ :=
  ([1515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part019 : ℚ :=
  (1935187877 : ℚ) / 8193638400000

def SurrogateDiagonalTailChunk000Sub000Block035Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1515
    = surrogateDiagTailX0RatChunk000Sub000Block035Part019

theorem surrogateDiagonalTailChunk000Sub000Block035Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part019] using hcert

def TailChunk000Sub000Block035Part020SupportExplicit : Finset ℕ :=
  ([1517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part020 : ℚ :=
  (16470741997 : ℚ) / 430067692339200

def SurrogateDiagonalTailChunk000Sub000Block035Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1517
    = surrogateDiagTailX0RatChunk000Sub000Block035Part020

theorem surrogateDiagonalTailChunk000Sub000Block035Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part020] using hcert

def TailChunk000Sub000Block035Part021SupportExplicit : Finset ℕ :=
  ([1518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part021 : ℚ :=
  (5675667301 : ℚ) / 3748845619200

def SurrogateDiagonalTailChunk000Sub000Block035Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1518
    = surrogateDiagTailX0RatChunk000Sub000Block035Part021

theorem surrogateDiagonalTailChunk000Sub000Block035Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part021] using hcert

def TailChunk000Sub000Block035Part022SupportExplicit : Finset ℕ :=
  ([1522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part022 : ℚ :=
  (578541879 : ℚ) / 2224589895680

def SurrogateDiagonalTailChunk000Sub000Block035Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1522
    = surrogateDiagTailX0RatChunk000Sub000Block035Part022

theorem surrogateDiagonalTailChunk000Sub000Block035Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part022] using hcert

def TailChunk000Sub000Block035Part023SupportExplicit : Finset ℕ :=
  ([1523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part023 : ℚ :=
  (144912574275 : ℚ) / 4472642784900376

def SurrogateDiagonalTailChunk000Sub000Block035Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1523
    = surrogateDiagTailX0RatChunk000Sub000Block035Part023

theorem surrogateDiagonalTailChunk000Sub000Block035Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part023] using hcert

def TailChunk000Sub000Block035Part024SupportExplicit : Finset ℕ :=
  ([1526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block035Part024 : ℚ :=
  (188517790375 : ℚ) / 440886582724608

def SurrogateDiagonalTailChunk000Sub000Block035Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1526
    = surrogateDiagTailX0RatChunk000Sub000Block035Part024

theorem surrogateDiagonalTailChunk000Sub000Block035Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block035Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block035Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block035Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block035Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block035Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block035HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block035Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block035Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block035Part000
    + surrogateDiagTailX0RatChunk000Sub000Block035Part001
    + surrogateDiagTailX0RatChunk000Sub000Block035Part002
    + surrogateDiagTailX0RatChunk000Sub000Block035Part003
    + surrogateDiagTailX0RatChunk000Sub000Block035Part004
    + surrogateDiagTailX0RatChunk000Sub000Block035Part005
    + surrogateDiagTailX0RatChunk000Sub000Block035Part006
    + surrogateDiagTailX0RatChunk000Sub000Block035Part007
    + surrogateDiagTailX0RatChunk000Sub000Block035Part008
    + surrogateDiagTailX0RatChunk000Sub000Block035Part009

def surrogateDiagonalTailChunk000Sub000Block035MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block035Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block035Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block035Part010
    + surrogateDiagTailX0RatChunk000Sub000Block035Part011
    + surrogateDiagTailX0RatChunk000Sub000Block035Part012
    + surrogateDiagTailX0RatChunk000Sub000Block035Part013
    + surrogateDiagTailX0RatChunk000Sub000Block035Part014
    + surrogateDiagTailX0RatChunk000Sub000Block035Part015
    + surrogateDiagTailX0RatChunk000Sub000Block035Part016
    + surrogateDiagTailX0RatChunk000Sub000Block035Part017
    + surrogateDiagTailX0RatChunk000Sub000Block035Part018
    + surrogateDiagTailX0RatChunk000Sub000Block035Part019

def surrogateDiagonalTailChunk000Sub000Block035TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block035Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block035Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block035Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block035Part020
    + surrogateDiagTailX0RatChunk000Sub000Block035Part021
    + surrogateDiagTailX0RatChunk000Sub000Block035Part022
    + surrogateDiagTailX0RatChunk000Sub000Block035Part023
    + surrogateDiagTailX0RatChunk000Sub000Block035Part024

def surrogateDiagonalTailChunk000Sub000Block035Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block035HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block035MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block035TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block035 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block035Part000
    + surrogateDiagTailX0RatChunk000Sub000Block035Part001
    + surrogateDiagTailX0RatChunk000Sub000Block035Part002
    + surrogateDiagTailX0RatChunk000Sub000Block035Part003
    + surrogateDiagTailX0RatChunk000Sub000Block035Part004
    + surrogateDiagTailX0RatChunk000Sub000Block035Part005
    + surrogateDiagTailX0RatChunk000Sub000Block035Part006
    + surrogateDiagTailX0RatChunk000Sub000Block035Part007
    + surrogateDiagTailX0RatChunk000Sub000Block035Part008
    + surrogateDiagTailX0RatChunk000Sub000Block035Part009
    + surrogateDiagTailX0RatChunk000Sub000Block035Part010
    + surrogateDiagTailX0RatChunk000Sub000Block035Part011
    + surrogateDiagTailX0RatChunk000Sub000Block035Part012
    + surrogateDiagTailX0RatChunk000Sub000Block035Part013
    + surrogateDiagTailX0RatChunk000Sub000Block035Part014
    + surrogateDiagTailX0RatChunk000Sub000Block035Part015
    + surrogateDiagTailX0RatChunk000Sub000Block035Part016
    + surrogateDiagTailX0RatChunk000Sub000Block035Part017
    + surrogateDiagTailX0RatChunk000Sub000Block035Part018
    + surrogateDiagTailX0RatChunk000Sub000Block035Part019
    + surrogateDiagTailX0RatChunk000Sub000Block035Part020
    + surrogateDiagTailX0RatChunk000Sub000Block035Part021
    + surrogateDiagTailX0RatChunk000Sub000Block035Part022
    + surrogateDiagTailX0RatChunk000Sub000Block035Part023
    + surrogateDiagTailX0RatChunk000Sub000Block035Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block035_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block035Head + surrogateDiagTailX0RatChunk000Sub000Block035Mid + surrogateDiagTailX0RatChunk000Sub000Block035Tail =
      surrogateDiagTailX0RatChunk000Sub000Block035 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block035Head surrogateDiagTailX0RatChunk000Sub000Block035Mid surrogateDiagTailX0RatChunk000Sub000Block035Tail surrogateDiagTailX0RatChunk000Sub000Block035
  ring

def SurrogateDiagonalTailChunk000Sub000Block035HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block035HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block035Head

def SurrogateDiagonalTailChunk000Sub000Block035MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block035MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block035Mid

def SurrogateDiagonalTailChunk000Sub000Block035TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block035TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block035Tail

theorem surrogateDiagonalTailChunk000Sub000Block035_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block035HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block035MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block035TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block035Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block035 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block035HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block035MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block035TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block035Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block035_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
