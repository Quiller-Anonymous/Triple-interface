import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [60,61). -/

/- Block 060 covers tail-support indices [1500,1525) and q from 2514 to 2558. -/

def TailChunk000Sub000Block060Part000SupportExplicit : Finset ℕ :=
  ([2514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part000 : ℚ :=
  (52541925 : ℚ) / 244227809408

def SurrogateDiagonalTailChunk000Sub000Block060Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2514
    = surrogateDiagTailX0RatChunk000Sub000Block060Part000

theorem surrogateDiagonalTailChunk000Sub000Block060Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part000] using hcert

def TailChunk000Sub000Block060Part001SupportExplicit : Finset ℕ :=
  ([2515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part001 : ℚ :=
  (307814150825 : ℚ) / 20325989510145024

def SurrogateDiagonalTailChunk000Sub000Block060Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2515
    = surrogateDiagTailX0RatChunk000Sub000Block060Part001

theorem surrogateDiagonalTailChunk000Sub000Block060Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part001] using hcert

def TailChunk000Sub000Block060Part002SupportExplicit : Finset ℕ :=
  ([2517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part002 : ℚ :=
  (105461475 : ℚ) / 3945173084288

def SurrogateDiagonalTailChunk000Sub000Block060Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2517
    = surrogateDiagTailX0RatChunk000Sub000Block060Part002

theorem surrogateDiagonalTailChunk000Sub000Block060Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part002] using hcert

def TailChunk000Sub000Block060Part003SupportExplicit : Finset ℕ :=
  ([2518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part003 : ℚ :=
  (198016243925 : ℚ) / 3131262144823524

def SurrogateDiagonalTailChunk000Sub000Block060Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2518
    = surrogateDiagTailX0RatChunk000Sub000Block060Part003

theorem surrogateDiagonalTailChunk000Sub000Block060Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part003] using hcert

def TailChunk000Sub000Block060Part004SupportExplicit : Finset ℕ :=
  ([2519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part004 : ℚ :=
  (5744301629 : ℚ) / 540575344650240

def SurrogateDiagonalTailChunk000Sub000Block060Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2519
    = surrogateDiagTailX0RatChunk000Sub000Block060Part004

theorem surrogateDiagonalTailChunk000Sub000Block060Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part004] using hcert

def TailChunk000Sub000Block060Part005SupportExplicit : Finset ℕ :=
  ([2521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part005 : ℚ :=
  (31770849559 : ℚ) / 4033564567603200

def SurrogateDiagonalTailChunk000Sub000Block060Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2521
    = surrogateDiagTailX0RatChunk000Sub000Block060Part005

theorem surrogateDiagonalTailChunk000Sub000Block060Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part005] using hcert

def TailChunk000Sub000Block060Part006SupportExplicit : Finset ℕ :=
  ([2522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part006 : ℚ :=
  (90802781875 : ℚ) / 1100973292388352

def SurrogateDiagonalTailChunk000Sub000Block060Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2522
    = surrogateDiagTailX0RatChunk000Sub000Block060Part006

theorem surrogateDiagonalTailChunk000Sub000Block060Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part006] using hcert

def TailChunk000Sub000Block060Part007SupportExplicit : Finset ℕ :=
  ([2526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part007 : ℚ :=
  (707263 : ℚ) / 3319142400

def SurrogateDiagonalTailChunk000Sub000Block060Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2526
    = surrogateDiagTailX0RatChunk000Sub000Block060Part007

theorem surrogateDiagonalTailChunk000Sub000Block060Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part007] using hcert

def TailChunk000Sub000Block060Part008SupportExplicit : Finset ℕ :=
  ([2530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part008 : ℚ :=
  (11125089961 : ℚ) / 59981529907200

def SurrogateDiagonalTailChunk000Sub000Block060Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2530
    = surrogateDiagTailX0RatChunk000Sub000Block060Part008

theorem surrogateDiagonalTailChunk000Sub000Block060Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part008] using hcert

def TailChunk000Sub000Block060Part009SupportExplicit : Finset ℕ :=
  ([2531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part009 : ℚ :=
  (32023399039 : ℚ) / 4097971511416200

def SurrogateDiagonalTailChunk000Sub000Block060Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2531
    = surrogateDiagTailX0RatChunk000Sub000Block060Part009

theorem surrogateDiagonalTailChunk000Sub000Block060Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part009] using hcert

def TailChunk000Sub000Block060Part010SupportExplicit : Finset ℕ :=
  ([2533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part010 : ℚ :=
  (249950042475 : ℚ) / 26207910463799296

def SurrogateDiagonalTailChunk000Sub000Block060Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2533
    = surrogateDiagTailX0RatChunk000Sub000Block060Part010

theorem surrogateDiagonalTailChunk000Sub000Block060Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part010] using hcert

def TailChunk000Sub000Block060Part011SupportExplicit : Finset ℕ :=
  ([2534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part011 : ℚ :=
  (168954247 : ℚ) / 1679951923200

def SurrogateDiagonalTailChunk000Sub000Block060Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2534
    = surrogateDiagTailX0RatChunk000Sub000Block060Part011

theorem surrogateDiagonalTailChunk000Sub000Block060Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part011] using hcert

def TailChunk000Sub000Block060Part012SupportExplicit : Finset ℕ :=
  ([2537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part012 : ℚ :=
  (193086497575 : ℚ) / 22012836272677152

def SurrogateDiagonalTailChunk000Sub000Block060Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2537
    = surrogateDiagTailX0RatChunk000Sub000Block060Part012

theorem surrogateDiagonalTailChunk000Sub000Block060Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part012] using hcert

def TailChunk000Sub000Block060Part013SupportExplicit : Finset ℕ :=
  ([2539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part013 : ℚ :=
  (805653961975 : ℚ) / 103751248113242568

def SurrogateDiagonalTailChunk000Sub000Block060Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2539
    = surrogateDiagTailX0RatChunk000Sub000Block060Part013

theorem surrogateDiagonalTailChunk000Sub000Block060Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part013] using hcert

def TailChunk000Sub000Block060Part014SupportExplicit : Finset ℕ :=
  ([2542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part014 : ℚ :=
  (15240098179 : ℚ) / 207401472000000

def SurrogateDiagonalTailChunk000Sub000Block060Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2542
    = surrogateDiagTailX0RatChunk000Sub000Block060Part014

theorem surrogateDiagonalTailChunk000Sub000Block060Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part014] using hcert

def TailChunk000Sub000Block060Part015SupportExplicit : Finset ℕ :=
  ([2543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part015 : ℚ :=
  (808194453775 : ℚ) / 104406862176235848

def SurrogateDiagonalTailChunk000Sub000Block060Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2543
    = surrogateDiagTailX0RatChunk000Sub000Block060Part015

theorem surrogateDiagonalTailChunk000Sub000Block060Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part015] using hcert

def TailChunk000Sub000Block060Part016SupportExplicit : Finset ℕ :=
  ([2545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part016 : ℚ :=
  (161634445375 : ℚ) / 10657655600259072

def SurrogateDiagonalTailChunk000Sub000Block060Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2545
    = surrogateDiagTailX0RatChunk000Sub000Block060Part016

theorem surrogateDiagonalTailChunk000Sub000Block060Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part016] using hcert

def TailChunk000Sub000Block060Part017SupportExplicit : Finset ℕ :=
  ([2546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part017 : ℚ :=
  (377777664925 : ℚ) / 4980725661783168

def SurrogateDiagonalTailChunk000Sub000Block060Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2546
    = surrogateDiagTailX0RatChunk000Sub000Block060Part017

theorem surrogateDiagonalTailChunk000Sub000Block060Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part017] using hcert

def TailChunk000Sub000Block060Part018SupportExplicit : Finset ℕ :=
  ([2549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part018 : ℚ :=
  (812012689975 : ℚ) / 105396103076654208

def SurrogateDiagonalTailChunk000Sub000Block060Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2549
    = surrogateDiagTailX0RatChunk000Sub000Block060Part018

theorem surrogateDiagonalTailChunk000Sub000Block060Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part018] using hcert

def TailChunk000Sub000Block060Part019SupportExplicit : Finset ℕ :=
  ([2551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part019 : ℚ :=
  (6507601 : ℚ) / 1691638510050

def SurrogateDiagonalTailChunk000Sub000Block060Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2551
    = surrogateDiagTailX0RatChunk000Sub000Block060Part019

theorem surrogateDiagonalTailChunk000Sub000Block060Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part019] using hcert

def TailChunk000Sub000Block060Part020SupportExplicit : Finset ℕ :=
  ([2553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part020 : ℚ :=
  (504764113525 : ℚ) / 15741552708845568

def SurrogateDiagonalTailChunk000Sub000Block060Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2553
    = surrogateDiagTailX0RatChunk000Sub000Block060Part020

theorem surrogateDiagonalTailChunk000Sub000Block060Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part020] using hcert

def TailChunk000Sub000Block060Part021SupportExplicit : Finset ℕ :=
  ([2554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part021 : ℚ :=
  (203718820325 : ℚ) / 3314359097991744

def SurrogateDiagonalTailChunk000Sub000Block060Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2554
    = surrogateDiagTailX0RatChunk000Sub000Block060Part021

theorem surrogateDiagonalTailChunk000Sub000Block060Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part021] using hcert

def TailChunk000Sub000Block060Part022SupportExplicit : Finset ℕ :=
  ([2555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part022 : ℚ :=
  (551182124425 : ℚ) / 22294709170864128

def SurrogateDiagonalTailChunk000Sub000Block060Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2555
    = surrogateDiagTailX0RatChunk000Sub000Block060Part022

theorem surrogateDiagonalTailChunk000Sub000Block060Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part022] using hcert

def TailChunk000Sub000Block060Part023SupportExplicit : Finset ℕ :=
  ([2557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part023 : ℚ :=
  (817117668775 : ℚ) / 106726005919237248

def SurrogateDiagonalTailChunk000Sub000Block060Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2557
    = surrogateDiagTailX0RatChunk000Sub000Block060Part023

theorem surrogateDiagonalTailChunk000Sub000Block060Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part023] using hcert

def TailChunk000Sub000Block060Part024SupportExplicit : Finset ℕ :=
  ([2558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block060Part024 : ℚ :=
  (204357436925 : ℚ) / 3335187684976164

def SurrogateDiagonalTailChunk000Sub000Block060Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2558
    = surrogateDiagTailX0RatChunk000Sub000Block060Part024

theorem surrogateDiagonalTailChunk000Sub000Block060Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block060Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block060Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block060Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block060Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block060Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block060HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block060Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block060Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block060Part000
    + surrogateDiagTailX0RatChunk000Sub000Block060Part001
    + surrogateDiagTailX0RatChunk000Sub000Block060Part002
    + surrogateDiagTailX0RatChunk000Sub000Block060Part003
    + surrogateDiagTailX0RatChunk000Sub000Block060Part004
    + surrogateDiagTailX0RatChunk000Sub000Block060Part005
    + surrogateDiagTailX0RatChunk000Sub000Block060Part006
    + surrogateDiagTailX0RatChunk000Sub000Block060Part007
    + surrogateDiagTailX0RatChunk000Sub000Block060Part008
    + surrogateDiagTailX0RatChunk000Sub000Block060Part009

def surrogateDiagonalTailChunk000Sub000Block060MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block060Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block060Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block060Part010
    + surrogateDiagTailX0RatChunk000Sub000Block060Part011
    + surrogateDiagTailX0RatChunk000Sub000Block060Part012
    + surrogateDiagTailX0RatChunk000Sub000Block060Part013
    + surrogateDiagTailX0RatChunk000Sub000Block060Part014
    + surrogateDiagTailX0RatChunk000Sub000Block060Part015
    + surrogateDiagTailX0RatChunk000Sub000Block060Part016
    + surrogateDiagTailX0RatChunk000Sub000Block060Part017
    + surrogateDiagTailX0RatChunk000Sub000Block060Part018
    + surrogateDiagTailX0RatChunk000Sub000Block060Part019

def surrogateDiagonalTailChunk000Sub000Block060TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block060Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block060Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block060Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block060Part020
    + surrogateDiagTailX0RatChunk000Sub000Block060Part021
    + surrogateDiagTailX0RatChunk000Sub000Block060Part022
    + surrogateDiagTailX0RatChunk000Sub000Block060Part023
    + surrogateDiagTailX0RatChunk000Sub000Block060Part024

def surrogateDiagonalTailChunk000Sub000Block060Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block060HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block060MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block060TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block060 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block060Part000
    + surrogateDiagTailX0RatChunk000Sub000Block060Part001
    + surrogateDiagTailX0RatChunk000Sub000Block060Part002
    + surrogateDiagTailX0RatChunk000Sub000Block060Part003
    + surrogateDiagTailX0RatChunk000Sub000Block060Part004
    + surrogateDiagTailX0RatChunk000Sub000Block060Part005
    + surrogateDiagTailX0RatChunk000Sub000Block060Part006
    + surrogateDiagTailX0RatChunk000Sub000Block060Part007
    + surrogateDiagTailX0RatChunk000Sub000Block060Part008
    + surrogateDiagTailX0RatChunk000Sub000Block060Part009
    + surrogateDiagTailX0RatChunk000Sub000Block060Part010
    + surrogateDiagTailX0RatChunk000Sub000Block060Part011
    + surrogateDiagTailX0RatChunk000Sub000Block060Part012
    + surrogateDiagTailX0RatChunk000Sub000Block060Part013
    + surrogateDiagTailX0RatChunk000Sub000Block060Part014
    + surrogateDiagTailX0RatChunk000Sub000Block060Part015
    + surrogateDiagTailX0RatChunk000Sub000Block060Part016
    + surrogateDiagTailX0RatChunk000Sub000Block060Part017
    + surrogateDiagTailX0RatChunk000Sub000Block060Part018
    + surrogateDiagTailX0RatChunk000Sub000Block060Part019
    + surrogateDiagTailX0RatChunk000Sub000Block060Part020
    + surrogateDiagTailX0RatChunk000Sub000Block060Part021
    + surrogateDiagTailX0RatChunk000Sub000Block060Part022
    + surrogateDiagTailX0RatChunk000Sub000Block060Part023
    + surrogateDiagTailX0RatChunk000Sub000Block060Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block060_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block060Head + surrogateDiagTailX0RatChunk000Sub000Block060Mid + surrogateDiagTailX0RatChunk000Sub000Block060Tail =
      surrogateDiagTailX0RatChunk000Sub000Block060 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block060Head surrogateDiagTailX0RatChunk000Sub000Block060Mid surrogateDiagTailX0RatChunk000Sub000Block060Tail surrogateDiagTailX0RatChunk000Sub000Block060
  ring

def SurrogateDiagonalTailChunk000Sub000Block060HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block060HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block060Head

def SurrogateDiagonalTailChunk000Sub000Block060MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block060MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block060Mid

def SurrogateDiagonalTailChunk000Sub000Block060TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block060TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block060Tail

theorem surrogateDiagonalTailChunk000Sub000Block060_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block060HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block060MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block060TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block060Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block060 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block060HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block060MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block060TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block060Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block060_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
