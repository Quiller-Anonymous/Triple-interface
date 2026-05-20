import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [10,11). -/

/- Block 010 covers tail-support indices [250,275) and q from 461 to 499. -/

def TailChunk000Sub000Block010Part000SupportExplicit : Finset ℕ :=
  ([461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part000 : ℚ :=
  (1166527769 : ℚ) / 895670298240

def SurrogateDiagonalTailChunk000Sub000Block010Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 461
    = surrogateDiagTailX0RatChunk000Sub000Block010Part000

theorem surrogateDiagonalTailChunk000Sub000Block010Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part000] using hcert

def TailChunk000Sub000Block010Part001SupportExplicit : Finset ℕ :=
  ([462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part001 : ℚ :=
  (11188999 : ℚ) / 153630720

def SurrogateDiagonalTailChunk000Sub000Block010Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 462
    = surrogateDiagTailX0RatChunk000Sub000Block010Part001

theorem surrogateDiagonalTailChunk000Sub000Block010Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part001] using hcert

def TailChunk000Sub000Block010Part002SupportExplicit : Finset ℕ :=
  ([463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part002 : ℚ :=
  (13371266375 : ℚ) / 10356239273688

def SurrogateDiagonalTailChunk000Sub000Block010Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 463
    = surrogateDiagTailX0RatChunk000Sub000Block010Part002

theorem surrogateDiagonalTailChunk000Sub000Block010Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part002] using hcert

def TailChunk000Sub000Block010Part003SupportExplicit : Finset ℕ :=
  ([465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part003 : ℚ :=
  (508597079 : ℚ) / 55307059200

def SurrogateDiagonalTailChunk000Sub000Block010Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 465
    = surrogateDiagTailX0RatChunk000Sub000Block010Part003

theorem surrogateDiagonalTailChunk000Sub000Block010Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part003] using hcert

def TailChunk000Sub000Block010Part004SupportExplicit : Finset ℕ :=
  ([466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part004 : ℚ :=
  (74333856025 : ℚ) / 7244005951488

def SurrogateDiagonalTailChunk000Sub000Block010Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 466
    = surrogateDiagTailX0RatChunk000Sub000Block010Part004

theorem surrogateDiagonalTailChunk000Sub000Block010Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part004] using hcert

def TailChunk000Sub000Block010Part005SupportExplicit : Finset ℕ :=
  ([467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part005 : ℚ :=
  (149636315125 : ℚ) / 117915399204168

def SurrogateDiagonalTailChunk000Sub000Block010Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 467
    = surrogateDiagTailX0RatChunk000Sub000Block010Part005

theorem surrogateDiagonalTailChunk000Sub000Block010Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part005] using hcert

def TailChunk000Sub000Block010Part006SupportExplicit : Finset ℕ :=
  ([469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part006 : ℚ :=
  (117576258025 : ℚ) / 61490440268928

def SurrogateDiagonalTailChunk000Sub000Block010Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 469
    = surrogateDiagTailX0RatChunk000Sub000Block010Part006

theorem surrogateDiagonalTailChunk000Sub000Block010Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part006] using hcert

def TailChunk000Sub000Block010Part007SupportExplicit : Finset ℕ :=
  ([470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part007 : ℚ :=
  (18971095125 : ℚ) / 955381651456

def SurrogateDiagonalTailChunk000Sub000Block010Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 470
    = surrogateDiagTailX0RatChunk000Sub000Block010Part007

theorem surrogateDiagonalTailChunk000Sub000Block010Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part007] using hcert

def TailChunk000Sub000Block010Part008SupportExplicit : Finset ℕ :=
  ([471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part008 : ℚ :=
  (6219103225 : ℚ) / 1480898360448

def SurrogateDiagonalTailChunk000Sub000Block010Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 471
    = surrogateDiagTailX0RatChunk000Sub000Block010Part008

theorem surrogateDiagonalTailChunk000Sub000Block010Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part008] using hcert

def TailChunk000Sub000Block010Part009SupportExplicit : Finset ℕ :=
  ([473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part009 : ℚ :=
  (5005171831 : ℚ) / 3112318339200

def SurrogateDiagonalTailChunk000Sub000Block010Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 473
    = surrogateDiagTailX0RatChunk000Sub000Block010Part009

theorem surrogateDiagonalTailChunk000Sub000Block010Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part009] using hcert

def TailChunk000Sub000Block010Part010SupportExplicit : Finset ℕ :=
  ([474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part010 : ℚ :=
  (1617625 : ℚ) / 49353408

def SurrogateDiagonalTailChunk000Sub000Block010Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 474
    = surrogateDiagTailX0RatChunk000Sub000Block010Part010

theorem surrogateDiagonalTailChunk000Sub000Block010Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part010] using hcert

def TailChunk000Sub000Block010Part011SupportExplicit : Finset ℕ :=
  ([478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part011 : ℚ :=
  (2092056625 : ℚ) / 235969444452

def SurrogateDiagonalTailChunk000Sub000Block010Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 478
    = surrogateDiagTailX0RatChunk000Sub000Block010Part011

theorem surrogateDiagonalTailChunk000Sub000Block010Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part011] using hcert

def TailChunk000Sub000Block010Part012SupportExplicit : Finset ℕ :=
  ([479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part012 : ℚ :=
  (157425206125 : ℚ) / 130538448109128

def SurrogateDiagonalTailChunk000Sub000Block010Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 479
    = surrogateDiagTailX0RatChunk000Sub000Block010Part012

theorem surrogateDiagonalTailChunk000Sub000Block010Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part012] using hcert

def TailChunk000Sub000Block010Part013SupportExplicit : Finset ℕ :=
  ([481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part013 : ℚ :=
  (4831345375 : ℚ) / 3225507692544

def SurrogateDiagonalTailChunk000Sub000Block010Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 481
    = surrogateDiagTailX0RatChunk000Sub000Block010Part013

theorem surrogateDiagonalTailChunk000Sub000Block010Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part013] using hcert

def TailChunk000Sub000Block010Part014SupportExplicit : Finset ℕ :=
  ([482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part014 : ℚ :=
  (33745061 : ℚ) / 3687137280

def SurrogateDiagonalTailChunk000Sub000Block010Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 482
    = surrogateDiagTailX0RatChunk000Sub000Block010Part014

theorem surrogateDiagonalTailChunk000Sub000Block010Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part014] using hcert

def TailChunk000Sub000Block010Part015SupportExplicit : Finset ℕ :=
  ([483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part015 : ℚ :=
  (3010607075 : ℚ) / 449861474304

def SurrogateDiagonalTailChunk000Sub000Block010Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 483
    = surrogateDiagTailX0RatChunk000Sub000Block010Part015

theorem surrogateDiagonalTailChunk000Sub000Block010Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part015] using hcert

def TailChunk000Sub000Block010Part016SupportExplicit : Finset ℕ :=
  ([485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part016 : ℚ :=
  (126253653775 : ℚ) / 54369051475968

def SurrogateDiagonalTailChunk000Sub000Block010Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 485
    = surrogateDiagTailX0RatChunk000Sub000Block010Part016

theorem surrogateDiagonalTailChunk000Sub000Block010Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part016] using hcert

def TailChunk000Sub000Block010Part017SupportExplicit : Finset ℕ :=
  ([487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part017 : ℚ :=
  (147963809875 : ℚ) / 139499270315208

def SurrogateDiagonalTailChunk000Sub000Block010Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 487
    = surrogateDiagTailX0RatChunk000Sub000Block010Part017

theorem surrogateDiagonalTailChunk000Sub000Block010Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part017] using hcert

def TailChunk000Sub000Block010Part018SupportExplicit : Finset ℕ :=
  ([489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part018 : ℚ :=
  (25174091425 : ℚ) / 6888852855072

def SurrogateDiagonalTailChunk000Sub000Block010Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 489
    = surrogateDiagTailX0RatChunk000Sub000Block010Part018

theorem surrogateDiagonalTailChunk000Sub000Block010Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part018] using hcert

def TailChunk000Sub000Block010Part019SupportExplicit : Finset ℕ :=
  ([491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part019 : ℚ :=
  (171890753 : ℚ) / 164741541720

def SurrogateDiagonalTailChunk000Sub000Block010Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 491
    = surrogateDiagTailX0RatChunk000Sub000Block010Part019

theorem surrogateDiagonalTailChunk000Sub000Block010Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part019] using hcert

def TailChunk000Sub000Block010Part020SupportExplicit : Finset ℕ :=
  ([493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part020 : ℚ :=
  (34558416475 : ℚ) / 25181345021952

def SurrogateDiagonalTailChunk000Sub000Block010Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 493
    = surrogateDiagTailX0RatChunk000Sub000Block010Part020

theorem surrogateDiagonalTailChunk000Sub000Block010Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part020] using hcert

def TailChunk000Sub000Block010Part021SupportExplicit : Finset ℕ :=
  ([494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part021 : ℚ :=
  (8351546975 : ℚ) / 680380528896

def SurrogateDiagonalTailChunk000Sub000Block010Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 494
    = surrogateDiagTailX0RatChunk000Sub000Block010Part021

theorem surrogateDiagonalTailChunk000Sub000Block010Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part021] using hcert

def TailChunk000Sub000Block010Part022SupportExplicit : Finset ℕ :=
  ([497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part022 : ℚ :=
  (82856687 : ℚ) / 49401878400

def SurrogateDiagonalTailChunk000Sub000Block010Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 497
    = surrogateDiagTailX0RatChunk000Sub000Block010Part022

theorem surrogateDiagonalTailChunk000Sub000Block010Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part022] using hcert

def TailChunk000Sub000Block010Part023SupportExplicit : Finset ℕ :=
  ([498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part023 : ℚ :=
  (10209525 : ℚ) / 361697408

def SurrogateDiagonalTailChunk000Sub000Block010Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 498
    = surrogateDiagTailX0RatChunk000Sub000Block010Part023

theorem surrogateDiagonalTailChunk000Sub000Block010Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part023] using hcert

def TailChunk000Sub000Block010Part024SupportExplicit : Finset ℕ :=
  ([499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block010Part024 : ℚ :=
  (155345498875 : ℚ) / 153795713032008

def SurrogateDiagonalTailChunk000Sub000Block010Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 499
    = surrogateDiagTailX0RatChunk000Sub000Block010Part024

theorem surrogateDiagonalTailChunk000Sub000Block010Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block010Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block010Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block010Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block010Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block010Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block010HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block010Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block010Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block010Part000
    + surrogateDiagTailX0RatChunk000Sub000Block010Part001
    + surrogateDiagTailX0RatChunk000Sub000Block010Part002
    + surrogateDiagTailX0RatChunk000Sub000Block010Part003
    + surrogateDiagTailX0RatChunk000Sub000Block010Part004
    + surrogateDiagTailX0RatChunk000Sub000Block010Part005
    + surrogateDiagTailX0RatChunk000Sub000Block010Part006
    + surrogateDiagTailX0RatChunk000Sub000Block010Part007
    + surrogateDiagTailX0RatChunk000Sub000Block010Part008
    + surrogateDiagTailX0RatChunk000Sub000Block010Part009

def surrogateDiagonalTailChunk000Sub000Block010MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block010Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block010Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block010Part010
    + surrogateDiagTailX0RatChunk000Sub000Block010Part011
    + surrogateDiagTailX0RatChunk000Sub000Block010Part012
    + surrogateDiagTailX0RatChunk000Sub000Block010Part013
    + surrogateDiagTailX0RatChunk000Sub000Block010Part014
    + surrogateDiagTailX0RatChunk000Sub000Block010Part015
    + surrogateDiagTailX0RatChunk000Sub000Block010Part016
    + surrogateDiagTailX0RatChunk000Sub000Block010Part017
    + surrogateDiagTailX0RatChunk000Sub000Block010Part018
    + surrogateDiagTailX0RatChunk000Sub000Block010Part019

def surrogateDiagonalTailChunk000Sub000Block010TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block010Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block010Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block010Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block010Part020
    + surrogateDiagTailX0RatChunk000Sub000Block010Part021
    + surrogateDiagTailX0RatChunk000Sub000Block010Part022
    + surrogateDiagTailX0RatChunk000Sub000Block010Part023
    + surrogateDiagTailX0RatChunk000Sub000Block010Part024

def surrogateDiagonalTailChunk000Sub000Block010Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block010HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block010MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block010TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block010 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block010Part000
    + surrogateDiagTailX0RatChunk000Sub000Block010Part001
    + surrogateDiagTailX0RatChunk000Sub000Block010Part002
    + surrogateDiagTailX0RatChunk000Sub000Block010Part003
    + surrogateDiagTailX0RatChunk000Sub000Block010Part004
    + surrogateDiagTailX0RatChunk000Sub000Block010Part005
    + surrogateDiagTailX0RatChunk000Sub000Block010Part006
    + surrogateDiagTailX0RatChunk000Sub000Block010Part007
    + surrogateDiagTailX0RatChunk000Sub000Block010Part008
    + surrogateDiagTailX0RatChunk000Sub000Block010Part009
    + surrogateDiagTailX0RatChunk000Sub000Block010Part010
    + surrogateDiagTailX0RatChunk000Sub000Block010Part011
    + surrogateDiagTailX0RatChunk000Sub000Block010Part012
    + surrogateDiagTailX0RatChunk000Sub000Block010Part013
    + surrogateDiagTailX0RatChunk000Sub000Block010Part014
    + surrogateDiagTailX0RatChunk000Sub000Block010Part015
    + surrogateDiagTailX0RatChunk000Sub000Block010Part016
    + surrogateDiagTailX0RatChunk000Sub000Block010Part017
    + surrogateDiagTailX0RatChunk000Sub000Block010Part018
    + surrogateDiagTailX0RatChunk000Sub000Block010Part019
    + surrogateDiagTailX0RatChunk000Sub000Block010Part020
    + surrogateDiagTailX0RatChunk000Sub000Block010Part021
    + surrogateDiagTailX0RatChunk000Sub000Block010Part022
    + surrogateDiagTailX0RatChunk000Sub000Block010Part023
    + surrogateDiagTailX0RatChunk000Sub000Block010Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block010_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block010Head + surrogateDiagTailX0RatChunk000Sub000Block010Mid + surrogateDiagTailX0RatChunk000Sub000Block010Tail =
      surrogateDiagTailX0RatChunk000Sub000Block010 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block010Head surrogateDiagTailX0RatChunk000Sub000Block010Mid surrogateDiagTailX0RatChunk000Sub000Block010Tail surrogateDiagTailX0RatChunk000Sub000Block010
  ring

def SurrogateDiagonalTailChunk000Sub000Block010HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block010HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block010Head

def SurrogateDiagonalTailChunk000Sub000Block010MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block010MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block010Mid

def SurrogateDiagonalTailChunk000Sub000Block010TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block010TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block010Tail

theorem surrogateDiagonalTailChunk000Sub000Block010_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block010HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block010MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block010TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block010Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block010 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block010HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block010MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block010TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block010Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block010_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
