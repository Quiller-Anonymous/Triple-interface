import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [34,35). -/

/- Block 034 covers tail-support indices [850,875) and q from 1443 to 1486. -/

def TailChunk000Sub000Block034Part000SupportExplicit : Finset ℕ :=
  ([1443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part000 : ℚ :=
  (9233536625 : ℚ) / 51608123080704

def SurrogateDiagonalTailChunk000Sub000Block034Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1443
    = surrogateDiagTailX0RatChunk000Sub000Block034Part000

theorem surrogateDiagonalTailChunk000Sub000Block034Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part000] using hcert

def TailChunk000Sub000Block034Part001SupportExplicit : Finset ℕ :=
  ([1446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part001 : ℚ :=
  (20243 : ℚ) / 17694720

def SurrogateDiagonalTailChunk000Sub000Block034Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1446
    = surrogateDiagTailX0RatChunk000Sub000Block034Part001

theorem surrogateDiagonalTailChunk000Sub000Block034Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part001] using hcert

def TailChunk000Sub000Block034Part002SupportExplicit : Finset ℕ :=
  ([1447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part002 : ℚ :=
  (43603572425 : ℚ) / 1214667806944392

def SurrogateDiagonalTailChunk000Sub000Block034Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1447
    = surrogateDiagTailX0RatChunk000Sub000Block034Part002

theorem surrogateDiagonalTailChunk000Sub000Block034Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part002] using hcert

def TailChunk000Sub000Block034Part003SupportExplicit : Finset ℕ :=
  ([1451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part003 : ℚ :=
  (10520688797 : ℚ) / 221069517562500

def SurrogateDiagonalTailChunk000Sub000Block034Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1451
    = surrogateDiagTailX0RatChunk000Sub000Block034Part003

theorem surrogateDiagonalTailChunk000Sub000Block034Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part003] using hcert

def TailChunk000Sub000Block034Part004SupportExplicit : Finset ℕ :=
  ([1453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part004 : ℚ :=
  (43965927425 : ℚ) / 1234954095990912

def SurrogateDiagonalTailChunk000Sub000Block034Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1453
    = surrogateDiagTailX0RatChunk000Sub000Block034Part004

theorem surrogateDiagonalTailChunk000Sub000Block034Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part004] using hcert

def TailChunk000Sub000Block034Part005SupportExplicit : Finset ℕ :=
  ([1454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part005 : ℚ :=
  (20995814525 : ℚ) / 63151061726808

def SurrogateDiagonalTailChunk000Sub000Block034Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1454
    = surrogateDiagTailX0RatChunk000Sub000Block034Part005

theorem surrogateDiagonalTailChunk000Sub000Block034Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part005] using hcert

def TailChunk000Sub000Block034Part006SupportExplicit : Finset ℕ :=
  ([1455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part006 : ℚ :=
  (260567848225 : ℚ) / 869904823615488

def SurrogateDiagonalTailChunk000Sub000Block034Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1455
    = surrogateDiagTailX0RatChunk000Sub000Block034Part006

theorem surrogateDiagonalTailChunk000Sub000Block034Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part006] using hcert

def TailChunk000Sub000Block034Part007SupportExplicit : Finset ℕ :=
  ([1457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part007 : ℚ :=
  (7599035471 : ℚ) / 181373235393600

def SurrogateDiagonalTailChunk000Sub000Block034Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1457
    = surrogateDiagTailX0RatChunk000Sub000Block034Part007

theorem surrogateDiagonalTailChunk000Sub000Block034Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part007] using hcert

def TailChunk000Sub000Block034Part008SupportExplicit : Finset ℕ :=
  ([1459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part008 : ℚ :=
  (265925473925 : ℚ) / 5649720447765924

def SurrogateDiagonalTailChunk000Sub000Block034Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1459
    = surrogateDiagTailX0RatChunk000Sub000Block034Part008

theorem surrogateDiagonalTailChunk000Sub000Block034Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part008] using hcert

def TailChunk000Sub000Block034Part009SupportExplicit : Finset ℕ :=
  ([1461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part009 : ℚ :=
  (281159944225 : ℚ) / 2231988325043328

def SurrogateDiagonalTailChunk000Sub000Block034Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1461
    = surrogateDiagTailX0RatChunk000Sub000Block034Part009

theorem surrogateDiagonalTailChunk000Sub000Block034Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part009] using hcert

def TailChunk000Sub000Block034Part010SupportExplicit : Finset ℕ :=
  ([1462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part010 : ℚ :=
  (107308814225 : ℚ) / 254961118347264

def SurrogateDiagonalTailChunk000Sub000Block034Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1462
    = surrogateDiagTailX0RatChunk000Sub000Block034Part010

theorem surrogateDiagonalTailChunk000Sub000Block034Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part010] using hcert

def TailChunk000Sub000Block034Part011SupportExplicit : Finset ℕ :=
  ([1463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part011 : ℚ :=
  (5040639407 : ℚ) / 45358701926400

def SurrogateDiagonalTailChunk000Sub000Block034Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1463
    = surrogateDiagTailX0RatChunk000Sub000Block034Part011

theorem surrogateDiagonalTailChunk000Sub000Block034Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part011] using hcert

def TailChunk000Sub000Block034Part012SupportExplicit : Finset ℕ :=
  ([1465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part012 : ℚ :=
  (331707102775 : ℚ) / 4653698359001088

def SurrogateDiagonalTailChunk000Sub000Block034Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1465
    = surrogateDiagTailX0RatChunk000Sub000Block034Part012

theorem surrogateDiagonalTailChunk000Sub000Block034Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part012] using hcert

def TailChunk000Sub000Block034Part013SupportExplicit : Finset ℕ :=
  ([1466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part013 : ℚ :=
  (2484961625 : ℚ) / 8863110507648

def SurrogateDiagonalTailChunk000Sub000Block034Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1466
    = surrogateDiagTailX0RatChunk000Sub000Block034Part013

theorem surrogateDiagonalTailChunk000Sub000Block034Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part013] using hcert

def TailChunk000Sub000Block034Part014SupportExplicit : Finset ℕ :=
  ([1469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part014 : ℚ :=
  (375409128925 : ℚ) / 8158755787112448

def SurrogateDiagonalTailChunk000Sub000Block034Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1469
    = surrogateDiagTailX0RatChunk000Sub000Block034Part014

theorem surrogateDiagonalTailChunk000Sub000Block034Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part014] using hcert

def TailChunk000Sub000Block034Part015SupportExplicit : Finset ℕ :=
  ([1471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part015 : ℚ :=
  (10812713477 : ℚ) / 233521135388100

def SurrogateDiagonalTailChunk000Sub000Block034Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1471
    = surrogateDiagTailX0RatChunk000Sub000Block034Part015

theorem surrogateDiagonalTailChunk000Sub000Block034Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part015] using hcert

def TailChunk000Sub000Block034Part016SupportExplicit : Finset ℕ :=
  ([1473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part016 : ℚ :=
  (11431872901 : ℚ) / 92255263363200

def SurrogateDiagonalTailChunk000Sub000Block034Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1473
    = surrogateDiagTailX0RatChunk000Sub000Block034Part016

theorem surrogateDiagonalTailChunk000Sub000Block034Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part016] using hcert

def TailChunk000Sub000Block034Part017SupportExplicit : Finset ℕ :=
  ([1474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part017 : ℚ :=
  (8488403893 : ℚ) / 18978530947200

def SurrogateDiagonalTailChunk000Sub000Block034Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1474
    = surrogateDiagTailX0RatChunk000Sub000Block034Part017

theorem surrogateDiagonalTailChunk000Sub000Block034Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part017] using hcert

def TailChunk000Sub000Block034Part018SupportExplicit : Finset ℕ :=
  ([1477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part018 : ℚ :=
  (25219693 : ℚ) / 444616905600

def SurrogateDiagonalTailChunk000Sub000Block034Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1477
    = surrogateDiagTailX0RatChunk000Sub000Block034Part018

theorem surrogateDiagonalTailChunk000Sub000Block034Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part018] using hcert

def TailChunk000Sub000Block034Part019SupportExplicit : Finset ℕ :=
  ([1478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part019 : ℚ :=
  (238641223975 : ℚ) / 741741035383368

def SurrogateDiagonalTailChunk000Sub000Block034Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1478
    = surrogateDiagTailX0RatChunk000Sub000Block034Part019

theorem surrogateDiagonalTailChunk000Sub000Block034Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part019] using hcert

def TailChunk000Sub000Block034Part020SupportExplicit : Finset ℕ :=
  ([1479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part020 : ℚ :=
  (263934210625 : ℚ) / 1611606081404928

def SurrogateDiagonalTailChunk000Sub000Block034Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1479
    = surrogateDiagTailX0RatChunk000Sub000Block034Part020

theorem surrogateDiagonalTailChunk000Sub000Block034Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part020] using hcert

def TailChunk000Sub000Block034Part021SupportExplicit : Finset ℕ :=
  ([1481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part021 : ℚ :=
  (5481209139 : ℚ) / 159960391014400

def SurrogateDiagonalTailChunk000Sub000Block034Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1481
    = surrogateDiagTailX0RatChunk000Sub000Block034Part021

theorem surrogateDiagonalTailChunk000Sub000Block034Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part021] using hcert

def TailChunk000Sub000Block034Part022SupportExplicit : Finset ℕ :=
  ([1482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part022 : ℚ :=
  (136522760725 : ℚ) / 87088707698688

def SurrogateDiagonalTailChunk000Sub000Block034Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1482
    = surrogateDiagTailX0RatChunk000Sub000Block034Part022

theorem surrogateDiagonalTailChunk000Sub000Block034Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part022] using hcert

def TailChunk000Sub000Block034Part023SupportExplicit : Finset ℕ :=
  ([1483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part023 : ℚ :=
  (45800193425 : ℚ) / 1340223300221832

def SurrogateDiagonalTailChunk000Sub000Block034Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1483
    = surrogateDiagTailX0RatChunk000Sub000Block034Part023

theorem surrogateDiagonalTailChunk000Sub000Block034Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part023] using hcert

def TailChunk000Sub000Block034Part024SupportExplicit : Finset ℕ :=
  ([1486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block034Part024 : ℚ :=
  (34461658825 : ℚ) / 108279050799864

def SurrogateDiagonalTailChunk000Sub000Block034Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1486
    = surrogateDiagTailX0RatChunk000Sub000Block034Part024

theorem surrogateDiagonalTailChunk000Sub000Block034Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block034Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block034Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block034Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block034Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block034Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block034HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block034Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block034Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block034Part000
    + surrogateDiagTailX0RatChunk000Sub000Block034Part001
    + surrogateDiagTailX0RatChunk000Sub000Block034Part002
    + surrogateDiagTailX0RatChunk000Sub000Block034Part003
    + surrogateDiagTailX0RatChunk000Sub000Block034Part004
    + surrogateDiagTailX0RatChunk000Sub000Block034Part005
    + surrogateDiagTailX0RatChunk000Sub000Block034Part006
    + surrogateDiagTailX0RatChunk000Sub000Block034Part007
    + surrogateDiagTailX0RatChunk000Sub000Block034Part008
    + surrogateDiagTailX0RatChunk000Sub000Block034Part009

def surrogateDiagonalTailChunk000Sub000Block034MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block034Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block034Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block034Part010
    + surrogateDiagTailX0RatChunk000Sub000Block034Part011
    + surrogateDiagTailX0RatChunk000Sub000Block034Part012
    + surrogateDiagTailX0RatChunk000Sub000Block034Part013
    + surrogateDiagTailX0RatChunk000Sub000Block034Part014
    + surrogateDiagTailX0RatChunk000Sub000Block034Part015
    + surrogateDiagTailX0RatChunk000Sub000Block034Part016
    + surrogateDiagTailX0RatChunk000Sub000Block034Part017
    + surrogateDiagTailX0RatChunk000Sub000Block034Part018
    + surrogateDiagTailX0RatChunk000Sub000Block034Part019

def surrogateDiagonalTailChunk000Sub000Block034TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block034Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block034Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block034Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block034Part020
    + surrogateDiagTailX0RatChunk000Sub000Block034Part021
    + surrogateDiagTailX0RatChunk000Sub000Block034Part022
    + surrogateDiagTailX0RatChunk000Sub000Block034Part023
    + surrogateDiagTailX0RatChunk000Sub000Block034Part024

def surrogateDiagonalTailChunk000Sub000Block034Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block034HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block034MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block034TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block034 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block034Part000
    + surrogateDiagTailX0RatChunk000Sub000Block034Part001
    + surrogateDiagTailX0RatChunk000Sub000Block034Part002
    + surrogateDiagTailX0RatChunk000Sub000Block034Part003
    + surrogateDiagTailX0RatChunk000Sub000Block034Part004
    + surrogateDiagTailX0RatChunk000Sub000Block034Part005
    + surrogateDiagTailX0RatChunk000Sub000Block034Part006
    + surrogateDiagTailX0RatChunk000Sub000Block034Part007
    + surrogateDiagTailX0RatChunk000Sub000Block034Part008
    + surrogateDiagTailX0RatChunk000Sub000Block034Part009
    + surrogateDiagTailX0RatChunk000Sub000Block034Part010
    + surrogateDiagTailX0RatChunk000Sub000Block034Part011
    + surrogateDiagTailX0RatChunk000Sub000Block034Part012
    + surrogateDiagTailX0RatChunk000Sub000Block034Part013
    + surrogateDiagTailX0RatChunk000Sub000Block034Part014
    + surrogateDiagTailX0RatChunk000Sub000Block034Part015
    + surrogateDiagTailX0RatChunk000Sub000Block034Part016
    + surrogateDiagTailX0RatChunk000Sub000Block034Part017
    + surrogateDiagTailX0RatChunk000Sub000Block034Part018
    + surrogateDiagTailX0RatChunk000Sub000Block034Part019
    + surrogateDiagTailX0RatChunk000Sub000Block034Part020
    + surrogateDiagTailX0RatChunk000Sub000Block034Part021
    + surrogateDiagTailX0RatChunk000Sub000Block034Part022
    + surrogateDiagTailX0RatChunk000Sub000Block034Part023
    + surrogateDiagTailX0RatChunk000Sub000Block034Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block034_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block034Head + surrogateDiagTailX0RatChunk000Sub000Block034Mid + surrogateDiagTailX0RatChunk000Sub000Block034Tail =
      surrogateDiagTailX0RatChunk000Sub000Block034 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block034Head surrogateDiagTailX0RatChunk000Sub000Block034Mid surrogateDiagTailX0RatChunk000Sub000Block034Tail surrogateDiagTailX0RatChunk000Sub000Block034
  ring

def SurrogateDiagonalTailChunk000Sub000Block034HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block034HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block034Head

def SurrogateDiagonalTailChunk000Sub000Block034MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block034MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block034Mid

def SurrogateDiagonalTailChunk000Sub000Block034TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block034TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block034Tail

theorem surrogateDiagonalTailChunk000Sub000Block034_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block034HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block034MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block034TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block034Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block034 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block034HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block034MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block034TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block034Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block034_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
