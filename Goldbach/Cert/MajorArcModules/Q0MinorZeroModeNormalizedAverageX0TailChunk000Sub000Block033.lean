import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [33,34). -/

/- Block 033 covers tail-support indices [825,850) and q from 1403 to 1442. -/

def TailChunk000Sub000Block033Part000SupportExplicit : Finset ℕ :=
  ([1403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part000 : ℚ :=
  (585508579 : ℚ) / 12652353964800

def SurrogateDiagonalTailChunk000Sub000Block033Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1403
    = surrogateDiagTailX0RatChunk000Sub000Block033Part000

theorem surrogateDiagonalTailChunk000Sub000Block033Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part000] using hcert

def TailChunk000Sub000Block033Part001SupportExplicit : Finset ℕ :=
  ([1405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part001 : ℚ :=
  (5113585629 : ℚ) / 52461135462400

def SurrogateDiagonalTailChunk000Sub000Block033Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1405
    = surrogateDiagTailX0RatChunk000Sub000Block033Part001

theorem surrogateDiagonalTailChunk000Sub000Block033Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part001] using hcert

def TailChunk000Sub000Block033Part002SupportExplicit : Finset ℕ :=
  ([1406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part002 : ℚ :=
  (199587973375 : ℚ) / 440886582724608

def SurrogateDiagonalTailChunk000Sub000Block033Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1406
    = surrogateDiagTailX0RatChunk000Sub000Block033Part002

theorem surrogateDiagonalTailChunk000Sub000Block033Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part002] using hcert

def TailChunk000Sub000Block033Part003SupportExplicit : Finset ℕ :=
  ([1407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part003 : ℚ :=
  (225624054325 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block033Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1407
    = surrogateDiagTailX0RatChunk000Sub000Block033Part003

theorem surrogateDiagonalTailChunk000Sub000Block033Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part003] using hcert

def TailChunk000Sub000Block033Part004SupportExplicit : Finset ℕ :=
  ([1409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part004 : ℚ :=
  (248011228925 : ℚ) / 4913686929997824

def SurrogateDiagonalTailChunk000Sub000Block033Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1409
    = surrogateDiagTailX0RatChunk000Sub000Block033Part004

theorem surrogateDiagonalTailChunk000Sub000Block033Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part004] using hcert

def TailChunk000Sub000Block033Part005SupportExplicit : Finset ℕ :=
  ([1410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part005 : ℚ :=
  (18948750975 : ℚ) / 7643053211648

def SurrogateDiagonalTailChunk000Sub000Block033Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1410
    = surrogateDiagTailX0RatChunk000Sub000Block033Part005

theorem surrogateDiagonalTailChunk000Sub000Block033Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part005] using hcert

def TailChunk000Sub000Block033Part006SupportExplicit : Finset ℕ :=
  ([1411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part006 : ℚ :=
  (117238762125 : ℚ) / 2469681476141056

def SurrogateDiagonalTailChunk000Sub000Block033Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1411
    = surrogateDiagTailX0RatChunk000Sub000Block033Part006

theorem surrogateDiagonalTailChunk000Sub000Block033Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part006] using hcert

def TailChunk000Sub000Block033Part007SupportExplicit : Finset ℕ :=
  ([1414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part007 : ℚ :=
  (3725362523 : ℚ) / 6481296000000

def SurrogateDiagonalTailChunk000Sub000Block033Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1414
    = surrogateDiagTailX0RatChunk000Sub000Block033Part007

theorem surrogateDiagonalTailChunk000Sub000Block033Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part007] using hcert

def TailChunk000Sub000Block033Part008SupportExplicit : Finset ℕ :=
  ([1415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part008 : ℚ :=
  (157213295975 : ℚ) / 2024106044580864

def SurrogateDiagonalTailChunk000Sub000Block033Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1415
    = surrogateDiagTailX0RatChunk000Sub000Block033Part008

theorem surrogateDiagonalTailChunk000Sub000Block033Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part008] using hcert

def TailChunk000Sub000Block033Part009SupportExplicit : Finset ℕ :=
  ([1417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part009 : ℚ :=
  (454322441125 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub000Block033Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1417
    = surrogateDiagTailX0RatChunk000Sub000Block033Part009

theorem surrogateDiagonalTailChunk000Sub000Block033Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part009] using hcert

def TailChunk000Sub000Block033Part010SupportExplicit : Finset ℕ :=
  ([1418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part010 : ℚ :=
  (219659029975 : ℚ) / 628289627038848

def SurrogateDiagonalTailChunk000Sub000Block033Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1418
    = surrogateDiagTailX0RatChunk000Sub000Block033Part010

theorem surrogateDiagonalTailChunk000Sub000Block033Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part010] using hcert

def TailChunk000Sub000Block033Part011SupportExplicit : Finset ℕ :=
  ([1419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part011 : ℚ :=
  (478706867 : ℚ) / 2489854671360

def SurrogateDiagonalTailChunk000Sub000Block033Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1419
    = surrogateDiagTailX0RatChunk000Sub000Block033Part011

theorem surrogateDiagonalTailChunk000Sub000Block033Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part011] using hcert

def TailChunk000Sub000Block033Part012SupportExplicit : Finset ℕ :=
  ([1423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part012 : ℚ :=
  (42169146425 : ℚ) / 1136011518832392

def SurrogateDiagonalTailChunk000Sub000Block033Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1423
    = surrogateDiagTailX0RatChunk000Sub000Block033Part012

theorem surrogateDiagonalTailChunk000Sub000Block033Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part012] using hcert

def TailChunk000Sub000Block033Part013SupportExplicit : Finset ℕ :=
  ([1426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part013 : ℚ :=
  (1647364397 : ℚ) / 3795706189440

def SurrogateDiagonalTailChunk000Sub000Block033Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1426
    = surrogateDiagTailX0RatChunk000Sub000Block033Part013

theorem surrogateDiagonalTailChunk000Sub000Block033Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part013] using hcert

def TailChunk000Sub000Block033Part014SupportExplicit : Finset ℕ :=
  ([1427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part014 : ℚ :=
  (127219654275 : ℚ) / 3446543039587096

def SurrogateDiagonalTailChunk000Sub000Block033Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1427
    = surrogateDiagTailX0RatChunk000Sub000Block033Part014

theorem surrogateDiagonalTailChunk000Sub000Block033Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part014] using hcert

def TailChunk000Sub000Block033Part015SupportExplicit : Finset ℕ :=
  ([1429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part015 : ℚ :=
  (255101971925 : ℚ) / 5198878800166464

def SurrogateDiagonalTailChunk000Sub000Block033Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1429
    = surrogateDiagTailX0RatChunk000Sub000Block033Part015

theorem surrogateDiagonalTailChunk000Sub000Block033Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part015] using hcert

def TailChunk000Sub000Block033Part016SupportExplicit : Finset ℕ :=
  ([1430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part016 : ℚ :=
  (600719119 : ℚ) / 530947768320

def SurrogateDiagonalTailChunk000Sub000Block033Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1430
    = surrogateDiagTailX0RatChunk000Sub000Block033Part016

theorem surrogateDiagonalTailChunk000Sub000Block033Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part016] using hcert

def TailChunk000Sub000Block033Part017SupportExplicit : Finset ℕ :=
  ([1433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part017 : ℚ :=
  (256532113325 : ℚ) / 5257374751417344

def SurrogateDiagonalTailChunk000Sub000Block033Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1433
    = surrogateDiagTailX0RatChunk000Sub000Block033Part017

theorem surrogateDiagonalTailChunk000Sub000Block033Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part017] using hcert

def TailChunk000Sub000Block033Part018SupportExplicit : Finset ℕ :=
  ([1434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part018 : ℚ :=
  (72900626525 : ℚ) / 64183688890944

def SurrogateDiagonalTailChunk000Sub000Block033Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1434
    = surrogateDiagTailX0RatChunk000Sub000Block033Part018

theorem surrogateDiagonalTailChunk000Sub000Block033Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part018] using hcert

def TailChunk000Sub000Block033Part019SupportExplicit : Finset ℕ :=
  ([1435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part019 : ℚ :=
  (605757239 : ℚ) / 4719535718400

def SurrogateDiagonalTailChunk000Sub000Block033Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1435
    = surrogateDiagTailX0RatChunk000Sub000Block033Part019

theorem surrogateDiagonalTailChunk000Sub000Block033Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part019] using hcert

def TailChunk000Sub000Block033Part020SupportExplicit : Finset ℕ :=
  ([1437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part020 : ℚ :=
  (329132383375 : ℚ) / 2088615169746048

def SurrogateDiagonalTailChunk000Sub000Block033Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1437
    = surrogateDiagTailX0RatChunk000Sub000Block033Part020

theorem surrogateDiagonalTailChunk000Sub000Block033Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part020] using hcert

def TailChunk000Sub000Block033Part021SupportExplicit : Finset ℕ :=
  ([1438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part021 : ℚ :=
  (225899032975 : ℚ) / 664545368937288

def SurrogateDiagonalTailChunk000Sub000Block033Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1438
    = surrogateDiagTailX0RatChunk000Sub000Block033Part021

theorem surrogateDiagonalTailChunk000Sub000Block033Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part021] using hcert

def TailChunk000Sub000Block033Part022SupportExplicit : Finset ℕ :=
  ([1439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part022 : ℚ :=
  (129368294475 : ℚ) / 3564028336748056

def SurrogateDiagonalTailChunk000Sub000Block033Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1439
    = surrogateDiagTailX0RatChunk000Sub000Block033Part022

theorem surrogateDiagonalTailChunk000Sub000Block033Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part022] using hcert

def TailChunk000Sub000Block033Part023SupportExplicit : Finset ℕ :=
  ([1441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part023 : ℚ :=
  (2307989543 : ℚ) / 35708390250000

def SurrogateDiagonalTailChunk000Sub000Block033Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1441
    = surrogateDiagTailX0RatChunk000Sub000Block033Part023

theorem surrogateDiagonalTailChunk000Sub000Block033Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part023] using hcert

def TailChunk000Sub000Block033Part024SupportExplicit : Finset ℕ :=
  ([1442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block033Part024 : ℚ :=
  (192417710425 : ℚ) / 350778161443968

def SurrogateDiagonalTailChunk000Sub000Block033Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1442
    = surrogateDiagTailX0RatChunk000Sub000Block033Part024

theorem surrogateDiagonalTailChunk000Sub000Block033Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block033Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block033Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block033Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block033Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block033Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block033HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block033Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block033Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block033Part000
    + surrogateDiagTailX0RatChunk000Sub000Block033Part001
    + surrogateDiagTailX0RatChunk000Sub000Block033Part002
    + surrogateDiagTailX0RatChunk000Sub000Block033Part003
    + surrogateDiagTailX0RatChunk000Sub000Block033Part004
    + surrogateDiagTailX0RatChunk000Sub000Block033Part005
    + surrogateDiagTailX0RatChunk000Sub000Block033Part006
    + surrogateDiagTailX0RatChunk000Sub000Block033Part007
    + surrogateDiagTailX0RatChunk000Sub000Block033Part008
    + surrogateDiagTailX0RatChunk000Sub000Block033Part009

def surrogateDiagonalTailChunk000Sub000Block033MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block033Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block033Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block033Part010
    + surrogateDiagTailX0RatChunk000Sub000Block033Part011
    + surrogateDiagTailX0RatChunk000Sub000Block033Part012
    + surrogateDiagTailX0RatChunk000Sub000Block033Part013
    + surrogateDiagTailX0RatChunk000Sub000Block033Part014
    + surrogateDiagTailX0RatChunk000Sub000Block033Part015
    + surrogateDiagTailX0RatChunk000Sub000Block033Part016
    + surrogateDiagTailX0RatChunk000Sub000Block033Part017
    + surrogateDiagTailX0RatChunk000Sub000Block033Part018
    + surrogateDiagTailX0RatChunk000Sub000Block033Part019

def surrogateDiagonalTailChunk000Sub000Block033TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block033Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block033Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block033Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block033Part020
    + surrogateDiagTailX0RatChunk000Sub000Block033Part021
    + surrogateDiagTailX0RatChunk000Sub000Block033Part022
    + surrogateDiagTailX0RatChunk000Sub000Block033Part023
    + surrogateDiagTailX0RatChunk000Sub000Block033Part024

def surrogateDiagonalTailChunk000Sub000Block033Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block033HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block033MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block033TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block033 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block033Part000
    + surrogateDiagTailX0RatChunk000Sub000Block033Part001
    + surrogateDiagTailX0RatChunk000Sub000Block033Part002
    + surrogateDiagTailX0RatChunk000Sub000Block033Part003
    + surrogateDiagTailX0RatChunk000Sub000Block033Part004
    + surrogateDiagTailX0RatChunk000Sub000Block033Part005
    + surrogateDiagTailX0RatChunk000Sub000Block033Part006
    + surrogateDiagTailX0RatChunk000Sub000Block033Part007
    + surrogateDiagTailX0RatChunk000Sub000Block033Part008
    + surrogateDiagTailX0RatChunk000Sub000Block033Part009
    + surrogateDiagTailX0RatChunk000Sub000Block033Part010
    + surrogateDiagTailX0RatChunk000Sub000Block033Part011
    + surrogateDiagTailX0RatChunk000Sub000Block033Part012
    + surrogateDiagTailX0RatChunk000Sub000Block033Part013
    + surrogateDiagTailX0RatChunk000Sub000Block033Part014
    + surrogateDiagTailX0RatChunk000Sub000Block033Part015
    + surrogateDiagTailX0RatChunk000Sub000Block033Part016
    + surrogateDiagTailX0RatChunk000Sub000Block033Part017
    + surrogateDiagTailX0RatChunk000Sub000Block033Part018
    + surrogateDiagTailX0RatChunk000Sub000Block033Part019
    + surrogateDiagTailX0RatChunk000Sub000Block033Part020
    + surrogateDiagTailX0RatChunk000Sub000Block033Part021
    + surrogateDiagTailX0RatChunk000Sub000Block033Part022
    + surrogateDiagTailX0RatChunk000Sub000Block033Part023
    + surrogateDiagTailX0RatChunk000Sub000Block033Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block033_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block033Head + surrogateDiagTailX0RatChunk000Sub000Block033Mid + surrogateDiagTailX0RatChunk000Sub000Block033Tail =
      surrogateDiagTailX0RatChunk000Sub000Block033 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block033Head surrogateDiagTailX0RatChunk000Sub000Block033Mid surrogateDiagTailX0RatChunk000Sub000Block033Tail surrogateDiagTailX0RatChunk000Sub000Block033
  ring

def SurrogateDiagonalTailChunk000Sub000Block033HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block033HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block033Head

def SurrogateDiagonalTailChunk000Sub000Block033MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block033MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block033Mid

def SurrogateDiagonalTailChunk000Sub000Block033TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block033TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block033Tail

theorem surrogateDiagonalTailChunk000Sub000Block033_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block033HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block033MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block033TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block033Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block033 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block033HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block033MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block033TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block033Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block033_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
