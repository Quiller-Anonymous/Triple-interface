import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [131,132). -/

/- Block 131 covers tail-support indices [3275,3300) and q from 5441 to 5479. -/

def TailChunk000Sub000Block131Part000SupportExplicit : Finset ℕ :=
  ([5441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part000 : ℚ :=
  (740112025 : ℚ) / 875956317192192

def SurrogateDiagonalTailChunk000Sub000Block131Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5441
    = surrogateDiagTailX0RatChunk000Sub000Block131Part000

theorem surrogateDiagonalTailChunk000Sub000Block131Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part000] using hcert

def TailChunk000Sub000Block131Part001SupportExplicit : Finset ℕ :=
  ([5442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part001 : ℚ :=
  (565051894225 : ℚ) / 26956259729751168

def SurrogateDiagonalTailChunk000Sub000Block131Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5442
    = surrogateDiagTailX0RatChunk000Sub000Block131Part001

theorem surrogateDiagonalTailChunk000Sub000Block131Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part001] using hcert

def TailChunk000Sub000Block131Part002SupportExplicit : Finset ℕ :=
  ([5443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part002 : ℚ :=
  (462910140625 : ℚ) / 548278249255916562

def SurrogateDiagonalTailChunk000Sub000Block131Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5443
    = surrogateDiagTailX0RatChunk000Sub000Block131Part002

theorem surrogateDiagonalTailChunk000Sub000Block131Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part002] using hcert

def TailChunk000Sub000Block131Part003SupportExplicit : Finset ℕ :=
  ([5446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part003 : ℚ :=
  (391485446225 : ℚ) / 36722206389003264

def SurrogateDiagonalTailChunk000Sub000Block131Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5446
    = surrogateDiagTailX0RatChunk000Sub000Block131Part003

theorem surrogateDiagonalTailChunk000Sub000Block131Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part003] using hcert

def TailChunk000Sub000Block131Part004SupportExplicit : Finset ℕ :=
  ([5447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part004 : ℚ :=
  (19280905525 : ℚ) / 17987644593236736

def SurrogateDiagonalTailChunk000Sub000Block131Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5447
    = surrogateDiagTailX0RatChunk000Sub000Block131Part004

theorem surrogateDiagonalTailChunk000Sub000Block131Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part004] using hcert

def TailChunk000Sub000Block131Part005SupportExplicit : Finset ℕ :=
  ([5449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part005 : ℚ :=
  (463931265625 : ℚ) / 550700236733501952

def SurrogateDiagonalTailChunk000Sub000Block131Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5449
    = surrogateDiagTailX0RatChunk000Sub000Block131Part005

theorem surrogateDiagonalTailChunk000Sub000Block131Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part005] using hcert

def TailChunk000Sub000Block131Part006SupportExplicit : Finset ℕ :=
  ([5451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part006 : ℚ :=
  (489953190275 : ℚ) / 173454663162553344

def SurrogateDiagonalTailChunk000Sub000Block131Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5451
    = surrogateDiagTailX0RatChunk000Sub000Block131Part006

theorem surrogateDiagonalTailChunk000Sub000Block131Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part006] using hcert

def TailChunk000Sub000Block131Part007SupportExplicit : Finset ℕ :=
  ([5453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part007 : ℚ :=
  (58441021663 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block131Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5453
    = surrogateDiagTailX0RatChunk000Sub000Block131Part007

theorem surrogateDiagonalTailChunk000Sub000Block131Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part007] using hcert

def TailChunk000Sub000Block131Part008SupportExplicit : Finset ℕ :=
  ([5455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part008 : ℚ :=
  (7061931083 : ℚ) / 4517964564230400

def SurrogateDiagonalTailChunk000Sub000Block131Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5455
    = surrogateDiagTailX0RatChunk000Sub000Block131Part008

theorem surrogateDiagonalTailChunk000Sub000Block131Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part008] using hcert

def TailChunk000Sub000Block131Part009SupportExplicit : Finset ℕ :=
  ([5457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part009 : ℚ :=
  (8994383825 : ℚ) / 2586069924642816

def SurrogateDiagonalTailChunk000Sub000Block131Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5457
    = surrogateDiagTailX0RatChunk000Sub000Block131Part009

theorem surrogateDiagonalTailChunk000Sub000Block131Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part009] using hcert

def TailChunk000Sub000Block131Part010SupportExplicit : Finset ℕ :=
  ([5458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part010 : ℚ :=
  (930743938975 : ℚ) / 138485506203568128

def SurrogateDiagonalTailChunk000Sub000Block131Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5458
    = surrogateDiagTailX0RatChunk000Sub000Block131Part010

theorem surrogateDiagonalTailChunk000Sub000Block131Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part010] using hcert

def TailChunk000Sub000Block131Part011SupportExplicit : Finset ℕ :=
  ([5459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part011 : ℚ :=
  (1805385550975 : ℚ) / 1978977791407638528

def SurrogateDiagonalTailChunk000Sub000Block131Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5459
    = surrogateDiagTailX0RatChunk000Sub000Block131Part011

theorem surrogateDiagonalTailChunk000Sub000Block131Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part011] using hcert

def TailChunk000Sub000Block131Part012SupportExplicit : Finset ℕ :=
  ([5461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part012 : ℚ :=
  (1801483744225 : ℚ) / 1961129176680094848

def SurrogateDiagonalTailChunk000Sub000Block131Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5461
    = surrogateDiagTailX0RatChunk000Sub000Block131Part012

theorem surrogateDiagonalTailChunk000Sub000Block131Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part012] using hcert

def TailChunk000Sub000Block131Part013SupportExplicit : Finset ℕ :=
  ([5462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part013 : ℚ :=
  (186459025 : ℚ) / 55556827553682

def SurrogateDiagonalTailChunk000Sub000Block131Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5462
    = surrogateDiagTailX0RatChunk000Sub000Block131Part013

theorem surrogateDiagonalTailChunk000Sub000Block131Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part013] using hcert

def TailChunk000Sub000Block131Part014SupportExplicit : Finset ℕ :=
  ([5465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part014 : ℚ :=
  (746064057875 : ℚ) / 455121531319762944

def SurrogateDiagonalTailChunk000Sub000Block131Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5465
    = surrogateDiagTailX0RatChunk000Sub000Block131Part014

theorem surrogateDiagonalTailChunk000Sub000Block131Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part014] using hcert

def TailChunk000Sub000Block131Part015SupportExplicit : Finset ℕ :=
  ([5466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part015 : ℚ :=
  (994719 : ℚ) / 43887975040

def SurrogateDiagonalTailChunk000Sub000Block131Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5466
    = surrogateDiagTailX0RatChunk000Sub000Block131Part015

theorem surrogateDiagonalTailChunk000Sub000Block131Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part015] using hcert

def TailChunk000Sub000Block131Part016SupportExplicit : Finset ℕ :=
  ([5467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part016 : ℚ :=
  (55618023799 : ℚ) / 31123183392000000

def SurrogateDiagonalTailChunk000Sub000Block131Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5467
    = surrogateDiagTailX0RatChunk000Sub000Block131Part016

theorem surrogateDiagonalTailChunk000Sub000Block131Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part016] using hcert

def TailChunk000Sub000Block131Part017SupportExplicit : Finset ℕ :=
  ([5469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part017 : ℚ :=
  (124550625 : ℚ) / 44081207439424

def SurrogateDiagonalTailChunk000Sub000Block131Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5469
    = surrogateDiagTailX0RatChunk000Sub000Block131Part017

theorem surrogateDiagonalTailChunk000Sub000Block131Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part017] using hcert

def TailChunk000Sub000Block131Part018SupportExplicit : Finset ℕ :=
  ([5470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part018 : ℚ :=
  (13482374225 : ℚ) / 1053522063240192

def SurrogateDiagonalTailChunk000Sub000Block131Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5470
    = surrogateDiagTailX0RatChunk000Sub000Block131Part018

theorem surrogateDiagonalTailChunk000Sub000Block131Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part018] using hcert

def TailChunk000Sub000Block131Part019SupportExplicit : Finset ℕ :=
  ([5471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part019 : ℚ :=
  (748296025 : ℚ) / 895439308861362

def SurrogateDiagonalTailChunk000Sub000Block131Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5471
    = surrogateDiagTailX0RatChunk000Sub000Block131Part019

theorem surrogateDiagonalTailChunk000Sub000Block131Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part019] using hcert

def TailChunk000Sub000Block131Part020SupportExplicit : Finset ℕ :=
  ([5473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part020 : ℚ :=
  (1268858639 : ℚ) / 1195130242252800

def SurrogateDiagonalTailChunk000Sub000Block131Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5473
    = surrogateDiagTailX0RatChunk000Sub000Block131Part020

theorem surrogateDiagonalTailChunk000Sub000Block131Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part020] using hcert

def TailChunk000Sub000Block131Part021SupportExplicit : Finset ℕ :=
  ([5474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part021 : ℚ :=
  (354175255175 : ℚ) / 24875540083113984

def SurrogateDiagonalTailChunk000Sub000Block131Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5474
    = surrogateDiagTailX0RatChunk000Sub000Block131Part021

theorem surrogateDiagonalTailChunk000Sub000Block131Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part021] using hcert

def TailChunk000Sub000Block131Part022SupportExplicit : Finset ℕ :=
  ([5477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part022 : ℚ :=
  (468711390625 : ℚ) / 562109111969885472

def SurrogateDiagonalTailChunk000Sub000Block131Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5477
    = surrogateDiagTailX0RatChunk000Sub000Block131Part022

theorem surrogateDiagonalTailChunk000Sub000Block131Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part022] using hcert

def TailChunk000Sub000Block131Part023SupportExplicit : Finset ℕ :=
  ([5478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part023 : ℚ :=
  (22239134377 : ℚ) / 723539494963200

def SurrogateDiagonalTailChunk000Sub000Block131Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5478
    = surrogateDiagTailX0RatChunk000Sub000Block131Part023

theorem surrogateDiagonalTailChunk000Sub000Block131Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part023] using hcert

def TailChunk000Sub000Block131Part024SupportExplicit : Finset ℕ :=
  ([5479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block131Part024 : ℚ :=
  (469053765625 : ℚ) / 562930758625407282

def SurrogateDiagonalTailChunk000Sub000Block131Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5479
    = surrogateDiagTailX0RatChunk000Sub000Block131Part024

theorem surrogateDiagonalTailChunk000Sub000Block131Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block131Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block131Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block131Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block131Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block131Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block131Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block131HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block131Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block131Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block131Part000
    + surrogateDiagTailX0RatChunk000Sub000Block131Part001
    + surrogateDiagTailX0RatChunk000Sub000Block131Part002
    + surrogateDiagTailX0RatChunk000Sub000Block131Part003
    + surrogateDiagTailX0RatChunk000Sub000Block131Part004
    + surrogateDiagTailX0RatChunk000Sub000Block131Part005
    + surrogateDiagTailX0RatChunk000Sub000Block131Part006
    + surrogateDiagTailX0RatChunk000Sub000Block131Part007
    + surrogateDiagTailX0RatChunk000Sub000Block131Part008
    + surrogateDiagTailX0RatChunk000Sub000Block131Part009

def surrogateDiagonalTailChunk000Sub000Block131MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block131Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block131Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block131Part010
    + surrogateDiagTailX0RatChunk000Sub000Block131Part011
    + surrogateDiagTailX0RatChunk000Sub000Block131Part012
    + surrogateDiagTailX0RatChunk000Sub000Block131Part013
    + surrogateDiagTailX0RatChunk000Sub000Block131Part014
    + surrogateDiagTailX0RatChunk000Sub000Block131Part015
    + surrogateDiagTailX0RatChunk000Sub000Block131Part016
    + surrogateDiagTailX0RatChunk000Sub000Block131Part017
    + surrogateDiagTailX0RatChunk000Sub000Block131Part018
    + surrogateDiagTailX0RatChunk000Sub000Block131Part019

def surrogateDiagonalTailChunk000Sub000Block131TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block131Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block131Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block131Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block131Part020
    + surrogateDiagTailX0RatChunk000Sub000Block131Part021
    + surrogateDiagTailX0RatChunk000Sub000Block131Part022
    + surrogateDiagTailX0RatChunk000Sub000Block131Part023
    + surrogateDiagTailX0RatChunk000Sub000Block131Part024

def surrogateDiagonalTailChunk000Sub000Block131Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block131HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block131MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block131TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block131 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block131Part000
    + surrogateDiagTailX0RatChunk000Sub000Block131Part001
    + surrogateDiagTailX0RatChunk000Sub000Block131Part002
    + surrogateDiagTailX0RatChunk000Sub000Block131Part003
    + surrogateDiagTailX0RatChunk000Sub000Block131Part004
    + surrogateDiagTailX0RatChunk000Sub000Block131Part005
    + surrogateDiagTailX0RatChunk000Sub000Block131Part006
    + surrogateDiagTailX0RatChunk000Sub000Block131Part007
    + surrogateDiagTailX0RatChunk000Sub000Block131Part008
    + surrogateDiagTailX0RatChunk000Sub000Block131Part009
    + surrogateDiagTailX0RatChunk000Sub000Block131Part010
    + surrogateDiagTailX0RatChunk000Sub000Block131Part011
    + surrogateDiagTailX0RatChunk000Sub000Block131Part012
    + surrogateDiagTailX0RatChunk000Sub000Block131Part013
    + surrogateDiagTailX0RatChunk000Sub000Block131Part014
    + surrogateDiagTailX0RatChunk000Sub000Block131Part015
    + surrogateDiagTailX0RatChunk000Sub000Block131Part016
    + surrogateDiagTailX0RatChunk000Sub000Block131Part017
    + surrogateDiagTailX0RatChunk000Sub000Block131Part018
    + surrogateDiagTailX0RatChunk000Sub000Block131Part019
    + surrogateDiagTailX0RatChunk000Sub000Block131Part020
    + surrogateDiagTailX0RatChunk000Sub000Block131Part021
    + surrogateDiagTailX0RatChunk000Sub000Block131Part022
    + surrogateDiagTailX0RatChunk000Sub000Block131Part023
    + surrogateDiagTailX0RatChunk000Sub000Block131Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block131_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block131Head + surrogateDiagTailX0RatChunk000Sub000Block131Mid + surrogateDiagTailX0RatChunk000Sub000Block131Tail =
      surrogateDiagTailX0RatChunk000Sub000Block131 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block131Head surrogateDiagTailX0RatChunk000Sub000Block131Mid surrogateDiagTailX0RatChunk000Sub000Block131Tail surrogateDiagTailX0RatChunk000Sub000Block131
  ring

def SurrogateDiagonalTailChunk000Sub000Block131HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block131HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block131Head

def SurrogateDiagonalTailChunk000Sub000Block131MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block131MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block131Mid

def SurrogateDiagonalTailChunk000Sub000Block131TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block131TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block131Tail

theorem surrogateDiagonalTailChunk000Sub000Block131_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block131HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block131MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block131TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block131Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block131 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block131HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block131MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block131TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block131Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block131_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
