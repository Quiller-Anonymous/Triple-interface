import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [59,60). -/

/- Block 059 covers tail-support indices [1475,1500) and q from 2474 to 2513. -/

def TailChunk000Sub000Block059Part000SupportExplicit : Finset ℕ :=
  ([2474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part000 : ℚ :=
  (191156362325 : ℚ) / 2917902299287104

def SurrogateDiagonalTailChunk000Sub000Block059Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2474
    = surrogateDiagTailX0RatChunk000Sub000Block059Part000

theorem surrogateDiagonalTailChunk000Sub000Block059Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part000] using hcert

def TailChunk000Sub000Block059Part001SupportExplicit : Finset ℕ :=
  ([2477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part001 : ℚ :=
  (766787736775 : ℚ) / 93978697210485888

def SurrogateDiagonalTailChunk000Sub000Block059Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2477
    = surrogateDiagTailX0RatChunk000Sub000Block059Part001

theorem surrogateDiagonalTailChunk000Sub000Block059Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part001] using hcert

def TailChunk000Sub000Block059Part002SupportExplicit : Finset ℕ :=
  ([2478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part002 : ℚ :=
  (216501742675 : ℚ) / 586764482070528

def SurrogateDiagonalTailChunk000Sub000Block059Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2478
    = surrogateDiagTailX0RatChunk000Sub000Block059Part002

theorem surrogateDiagonalTailChunk000Sub000Block059Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part002] using hcert

def TailChunk000Sub000Block059Part003SupportExplicit : Finset ℕ :=
  ([2479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part003 : ℚ :=
  (368383044875 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block059Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2479
    = surrogateDiagTailX0RatChunk000Sub000Block059Part003

theorem surrogateDiagonalTailChunk000Sub000Block059Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part003] using hcert

def TailChunk000Sub000Block059Part004SupportExplicit : Finset ℕ :=
  ([2481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part004 : ℚ :=
  (102466275 : ℚ) / 3724004321408

def SurrogateDiagonalTailChunk000Sub000Block059Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2481
    = surrogateDiagTailX0RatChunk000Sub000Block059Part004

theorem surrogateDiagonalTailChunk000Sub000Block059Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part004] using hcert

def TailChunk000Sub000Block059Part005SupportExplicit : Finset ℕ :=
  ([2482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part005 : ℚ :=
  (119171225275 : ℚ) / 1467964389851136

def SurrogateDiagonalTailChunk000Sub000Block059Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2482
    = surrogateDiagTailX0RatChunk000Sub000Block059Part005

theorem surrogateDiagonalTailChunk000Sub000Block059Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part005] using hcert

def TailChunk000Sub000Block059Part006SupportExplicit : Finset ℕ :=
  ([2483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part006 : ℚ :=
  (3539127683 : ℚ) / 337859590406400

def SurrogateDiagonalTailChunk000Sub000Block059Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2483
    = surrogateDiagTailX0RatChunk000Sub000Block059Part006

theorem surrogateDiagonalTailChunk000Sub000Block059Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part006] using hcert

def TailChunk000Sub000Block059Part007SupportExplicit : Finset ℕ :=
  ([2485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part007 : ℚ :=
  (10357231 : ℚ) / 395215027200

def SurrogateDiagonalTailChunk000Sub000Block059Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2485
    = surrogateDiagTailX0RatChunk000Sub000Block059Part007

theorem surrogateDiagonalTailChunk000Sub000Block059Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part007] using hcert

def TailChunk000Sub000Block059Part008SupportExplicit : Finset ℕ :=
  ([2486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part008 : ℚ :=
  (465218547 : ℚ) / 5246113546240

def SurrogateDiagonalTailChunk000Sub000Block059Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2486
    = surrogateDiagTailX0RatChunk000Sub000Block059Part008

theorem surrogateDiagonalTailChunk000Sub000Block059Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part008] using hcert

def TailChunk000Sub000Block059Part009SupportExplicit : Finset ℕ :=
  ([2487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part009 : ℚ :=
  (3813425 : ℚ) / 139266791424

def SurrogateDiagonalTailChunk000Sub000Block059Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2487
    = surrogateDiagTailX0RatChunk000Sub000Block059Part009

theorem surrogateDiagonalTailChunk000Sub000Block059Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part009] using hcert

def TailChunk000Sub000Block059Part010SupportExplicit : Finset ℕ :=
  ([2489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part010 : ℚ :=
  (1165119577 : ℚ) / 119952767196288

def SurrogateDiagonalTailChunk000Sub000Block059Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2489
    = surrogateDiagTailX0RatChunk000Sub000Block059Part010

theorem surrogateDiagonalTailChunk000Sub000Block059Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part010] using hcert

def TailChunk000Sub000Block059Part011SupportExplicit : Finset ℕ :=
  ([2490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part011 : ℚ :=
  (204230961775 : ℚ) / 463065276776448

def SurrogateDiagonalTailChunk000Sub000Block059Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2490
    = surrogateDiagTailX0RatChunk000Sub000Block059Part011

theorem surrogateDiagonalTailChunk000Sub000Block059Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part011] using hcert

def TailChunk000Sub000Block059Part012SupportExplicit : Finset ℕ :=
  ([2491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part012 : ℚ :=
  (745128106375 : ℚ) / 81859966041704448

def SurrogateDiagonalTailChunk000Sub000Block059Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2491
    = surrogateDiagTailX0RatChunk000Sub000Block059Part012

theorem surrogateDiagonalTailChunk000Sub000Block059Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part012] using hcert

def TailChunk000Sub000Block059Part013SupportExplicit : Finset ℕ :=
  ([2494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part013 : ℚ :=
  (6792635825 : ℚ) / 88565052828672

def SurrogateDiagonalTailChunk000Sub000Block059Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2494
    = surrogateDiagTailX0RatChunk000Sub000Block059Part013

theorem surrogateDiagonalTailChunk000Sub000Block059Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part013] using hcert

def TailChunk000Sub000Block059Part014SupportExplicit : Finset ℕ :=
  ([2495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part014 : ℚ :=
  (155345687875 : ℚ) / 9842925634048512

def SurrogateDiagonalTailChunk000Sub000Block059Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2495
    = surrogateDiagTailX0RatChunk000Sub000Block059Part014

theorem surrogateDiagonalTailChunk000Sub000Block059Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part014] using hcert

def TailChunk000Sub000Block059Part015SupportExplicit : Finset ℕ :=
  ([2497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part015 : ℚ :=
  (5644401653 : ℚ) / 521855905511040

def SurrogateDiagonalTailChunk000Sub000Block059Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2497
    = surrogateDiagTailX0RatChunk000Sub000Block059Part015

theorem surrogateDiagonalTailChunk000Sub000Block059Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part015] using hcert

def TailChunk000Sub000Block059Part016SupportExplicit : Finset ℕ :=
  ([2498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part016 : ℚ :=
  (194883124925 : ℚ) / 3032879842197504

def SurrogateDiagonalTailChunk000Sub000Block059Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2498
    = surrogateDiagTailX0RatChunk000Sub000Block059Part016

theorem surrogateDiagonalTailChunk000Sub000Block059Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part016] using hcert

def TailChunk000Sub000Block059Part017SupportExplicit : Finset ℕ :=
  ([2501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part017 : ℚ :=
  (30017999899 : ℚ) / 3318423552000000

def SurrogateDiagonalTailChunk000Sub000Block059Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2501
    = surrogateDiagTailX0RatChunk000Sub000Block059Part017

theorem surrogateDiagonalTailChunk000Sub000Block059Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part017] using hcert

def TailChunk000Sub000Block059Part018SupportExplicit : Finset ℕ :=
  ([2503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part018 : ℚ :=
  (782969499775 : ℚ) / 97988719025080008

def SurrogateDiagonalTailChunk000Sub000Block059Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2503
    = surrogateDiagTailX0RatChunk000Sub000Block059Part018

theorem surrogateDiagonalTailChunk000Sub000Block059Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part018] using hcert

def TailChunk000Sub000Block059Part019SupportExplicit : Finset ℕ :=
  ([2505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part019 : ℚ :=
  (409016683075 : ℚ) / 7777126426902528

def SurrogateDiagonalTailChunk000Sub000Block059Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2505
    = surrogateDiagTailX0RatChunk000Sub000Block059Part019

theorem surrogateDiagonalTailChunk000Sub000Block059Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part019] using hcert

def TailChunk000Sub000Block059Part020SupportExplicit : Finset ℕ :=
  ([2506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part020 : ℚ :=
  (37179205175 : ℚ) / 361467587221632

def SurrogateDiagonalTailChunk000Sub000Block059Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2506
    = surrogateDiagTailX0RatChunk000Sub000Block059Part020

theorem surrogateDiagonalTailChunk000Sub000Block059Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part020] using hcert

def TailChunk000Sub000Block059Part021SupportExplicit : Finset ℕ :=
  ([2507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part021 : ℚ :=
  (372348454175 : ℚ) / 39845805294265344

def SurrogateDiagonalTailChunk000Sub000Block059Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2507
    = surrogateDiagTailX0RatChunk000Sub000Block059Part021

theorem surrogateDiagonalTailChunk000Sub000Block059Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part021] using hcert

def TailChunk000Sub000Block059Part022SupportExplicit : Finset ℕ :=
  ([2509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part022 : ℚ :=
  (90340814525 : ℚ) / 8807786339106816

def SurrogateDiagonalTailChunk000Sub000Block059Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2509
    = surrogateDiagTailX0RatChunk000Sub000Block059Part022

theorem surrogateDiagonalTailChunk000Sub000Block059Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part022] using hcert

def TailChunk000Sub000Block059Part023SupportExplicit : Finset ℕ :=
  ([2510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part023 : ℚ :=
  (6198020357 : ℚ) / 50010000000000

def SurrogateDiagonalTailChunk000Sub000Block059Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2510
    = surrogateDiagTailX0RatChunk000Sub000Block059Part023

theorem surrogateDiagonalTailChunk000Sub000Block059Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part023] using hcert

def TailChunk000Sub000Block059Part024SupportExplicit : Finset ℕ :=
  ([2513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block059Part024 : ℚ :=
  (74985014825 : ℚ) / 5914546595344512

def SurrogateDiagonalTailChunk000Sub000Block059Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2513
    = surrogateDiagTailX0RatChunk000Sub000Block059Part024

theorem surrogateDiagonalTailChunk000Sub000Block059Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block059Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block059Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block059Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block059Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block059Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block059HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block059Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block059Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block059Part000
    + surrogateDiagTailX0RatChunk000Sub000Block059Part001
    + surrogateDiagTailX0RatChunk000Sub000Block059Part002
    + surrogateDiagTailX0RatChunk000Sub000Block059Part003
    + surrogateDiagTailX0RatChunk000Sub000Block059Part004
    + surrogateDiagTailX0RatChunk000Sub000Block059Part005
    + surrogateDiagTailX0RatChunk000Sub000Block059Part006
    + surrogateDiagTailX0RatChunk000Sub000Block059Part007
    + surrogateDiagTailX0RatChunk000Sub000Block059Part008
    + surrogateDiagTailX0RatChunk000Sub000Block059Part009

def surrogateDiagonalTailChunk000Sub000Block059MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block059Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block059Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block059Part010
    + surrogateDiagTailX0RatChunk000Sub000Block059Part011
    + surrogateDiagTailX0RatChunk000Sub000Block059Part012
    + surrogateDiagTailX0RatChunk000Sub000Block059Part013
    + surrogateDiagTailX0RatChunk000Sub000Block059Part014
    + surrogateDiagTailX0RatChunk000Sub000Block059Part015
    + surrogateDiagTailX0RatChunk000Sub000Block059Part016
    + surrogateDiagTailX0RatChunk000Sub000Block059Part017
    + surrogateDiagTailX0RatChunk000Sub000Block059Part018
    + surrogateDiagTailX0RatChunk000Sub000Block059Part019

def surrogateDiagonalTailChunk000Sub000Block059TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block059Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block059Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block059Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block059Part020
    + surrogateDiagTailX0RatChunk000Sub000Block059Part021
    + surrogateDiagTailX0RatChunk000Sub000Block059Part022
    + surrogateDiagTailX0RatChunk000Sub000Block059Part023
    + surrogateDiagTailX0RatChunk000Sub000Block059Part024

def surrogateDiagonalTailChunk000Sub000Block059Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block059HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block059MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block059TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block059 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block059Part000
    + surrogateDiagTailX0RatChunk000Sub000Block059Part001
    + surrogateDiagTailX0RatChunk000Sub000Block059Part002
    + surrogateDiagTailX0RatChunk000Sub000Block059Part003
    + surrogateDiagTailX0RatChunk000Sub000Block059Part004
    + surrogateDiagTailX0RatChunk000Sub000Block059Part005
    + surrogateDiagTailX0RatChunk000Sub000Block059Part006
    + surrogateDiagTailX0RatChunk000Sub000Block059Part007
    + surrogateDiagTailX0RatChunk000Sub000Block059Part008
    + surrogateDiagTailX0RatChunk000Sub000Block059Part009
    + surrogateDiagTailX0RatChunk000Sub000Block059Part010
    + surrogateDiagTailX0RatChunk000Sub000Block059Part011
    + surrogateDiagTailX0RatChunk000Sub000Block059Part012
    + surrogateDiagTailX0RatChunk000Sub000Block059Part013
    + surrogateDiagTailX0RatChunk000Sub000Block059Part014
    + surrogateDiagTailX0RatChunk000Sub000Block059Part015
    + surrogateDiagTailX0RatChunk000Sub000Block059Part016
    + surrogateDiagTailX0RatChunk000Sub000Block059Part017
    + surrogateDiagTailX0RatChunk000Sub000Block059Part018
    + surrogateDiagTailX0RatChunk000Sub000Block059Part019
    + surrogateDiagTailX0RatChunk000Sub000Block059Part020
    + surrogateDiagTailX0RatChunk000Sub000Block059Part021
    + surrogateDiagTailX0RatChunk000Sub000Block059Part022
    + surrogateDiagTailX0RatChunk000Sub000Block059Part023
    + surrogateDiagTailX0RatChunk000Sub000Block059Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block059_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block059Head + surrogateDiagTailX0RatChunk000Sub000Block059Mid + surrogateDiagTailX0RatChunk000Sub000Block059Tail =
      surrogateDiagTailX0RatChunk000Sub000Block059 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block059Head surrogateDiagTailX0RatChunk000Sub000Block059Mid surrogateDiagTailX0RatChunk000Sub000Block059Tail surrogateDiagTailX0RatChunk000Sub000Block059
  ring

def SurrogateDiagonalTailChunk000Sub000Block059HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block059HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block059Head

def SurrogateDiagonalTailChunk000Sub000Block059MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block059MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block059Mid

def SurrogateDiagonalTailChunk000Sub000Block059TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block059TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block059Tail

theorem surrogateDiagonalTailChunk000Sub000Block059_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block059HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block059MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block059TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block059Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block059 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block059HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block059MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block059TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block059Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block059_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
