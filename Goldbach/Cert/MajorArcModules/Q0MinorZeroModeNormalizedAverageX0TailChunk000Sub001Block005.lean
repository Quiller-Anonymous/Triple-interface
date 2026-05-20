import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [5,6). -/

/-- Block 005 covers tail-support indices [5125,5150) and q from 8482 to 8518. -/

def TailChunk000Sub001Block005Part000SupportExplicit : Finset ℕ :=
  ([8482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part000 : ℚ :=
  (89912418919 : ℚ) / 32325874058035200

def SurrogateDiagonalTailChunk000Sub001Block005Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8482
    = surrogateDiagTailX0RatChunk000Sub001Block005Part000

theorem surrogateDiagonalTailChunk000Sub001Block005Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part000] using hcert

def TailChunk000Sub001Block005Part001SupportExplicit : Finset ℕ :=
  ([8483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part001 : ℚ :=
  (4113217609375 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk000Sub001Block005Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8483
    = surrogateDiagTailX0RatChunk000Sub001Block005Part001

theorem surrogateDiagonalTailChunk000Sub001Block005Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part001] using hcert

def TailChunk000Sub001Block005Part002SupportExplicit : Finset ℕ :=
  ([8485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part002 : ℚ :=
  (1079240555775 : ℚ) / 1765423735222829056

def SurrogateDiagonalTailChunk000Sub001Block005Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8485
    = surrogateDiagTailX0RatChunk000Sub001Block005Part002

theorem surrogateDiagonalTailChunk000Sub001Block005Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part002] using hcert

def TailChunk000Sub001Block005Part003SupportExplicit : Finset ℕ :=
  ([8486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part003 : ℚ :=
  (2249931048775 : ℚ) / 809672736042015048

def SurrogateDiagonalTailChunk000Sub001Block005Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8486
    = surrogateDiagTailX0RatChunk000Sub001Block005Part003

theorem surrogateDiagonalTailChunk000Sub001Block005Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part003] using hcert

def TailChunk000Sub001Block005Part004SupportExplicit : Finset ℕ :=
  ([8489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part004 : ℚ :=
  (167347219525 : ℚ) / 390419035556032512

def SurrogateDiagonalTailChunk000Sub001Block005Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8489
    = surrogateDiagTailX0RatChunk000Sub001Block005Part004

theorem surrogateDiagonalTailChunk000Sub001Block005Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part004] using hcert

def TailChunk000Sub001Block005Part005SupportExplicit : Finset ℕ :=
  ([8490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part005 : ℚ :=
  (157217374375 : ℚ) / 16192848356646912

def SurrogateDiagonalTailChunk000Sub001Block005Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8490
    = surrogateDiagTailX0RatChunk000Sub001Block005Part005

theorem surrogateDiagonalTailChunk000Sub001Block005Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part005] using hcert

def TailChunk000Sub001Block005Part006SupportExplicit : Finset ℕ :=
  ([8491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part006 : ℚ :=
  (199054093475 : ℚ) / 388481046197584896

def SurrogateDiagonalTailChunk000Sub001Block005Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8491
    = surrogateDiagTailX0RatChunk000Sub001Block005Part006

theorem surrogateDiagonalTailChunk000Sub001Block005Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part006] using hcert

def TailChunk000Sub001Block005Part007SupportExplicit : Finset ℕ :=
  ([8493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part007 : ℚ :=
  (385694996975 : ℚ) / 335840040142553088

def SurrogateDiagonalTailChunk000Sub001Block005Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8493
    = surrogateDiagTailX0RatChunk000Sub001Block005Part007

theorem surrogateDiagonalTailChunk000Sub001Block005Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part007] using hcert

def TailChunk000Sub001Block005Part008SupportExplicit : Finset ℕ :=
  ([8494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part008 : ℚ :=
  (21830525429 : ℚ) / 13857902674329600

def SurrogateDiagonalTailChunk000Sub001Block005Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8494
    = surrogateDiagTailX0RatChunk000Sub001Block005Part008

theorem surrogateDiagonalTailChunk000Sub001Block005Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part008] using hcert

def TailChunk000Sub001Block005Part009SupportExplicit : Finset ℕ :=
  ([8495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part009 : ℚ :=
  (3245359355425 : ℚ) / 5321297842353358848

def SurrogateDiagonalTailChunk000Sub001Block005Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8495
    = surrogateDiagTailX0RatChunk000Sub001Block005Part009

theorem surrogateDiagonalTailChunk000Sub001Block005Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part009] using hcert

def TailChunk000Sub001Block005Part010SupportExplicit : Finset ℕ :=
  ([8497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part010 : ℚ :=
  (305184179675 : ℚ) / 798109268568686592

def SurrogateDiagonalTailChunk000Sub001Block005Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8497
    = surrogateDiagTailX0RatChunk000Sub001Block005Part010

theorem surrogateDiagonalTailChunk000Sub001Block005Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part010] using hcert

def TailChunk000Sub001Block005Part011SupportExplicit : Finset ℕ :=
  ([8498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part011 : ℚ :=
  (247252925875 : ℚ) / 109260294243070752

def SurrogateDiagonalTailChunk000Sub001Block005Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8498
    = surrogateDiagTailX0RatChunk000Sub001Block005Part011

theorem surrogateDiagonalTailChunk000Sub001Block005Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part011] using hcert

def TailChunk000Sub001Block005Part012SupportExplicit : Finset ℕ :=
  ([8499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part012 : ℚ :=
  (1253672938925 : ℚ) / 1286737156175560704

def SurrogateDiagonalTailChunk000Sub001Block005Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8499
    = surrogateDiagTailX0RatChunk000Sub001Block005Part012

theorem surrogateDiagonalTailChunk000Sub001Block005Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part012] using hcert

def TailChunk000Sub001Block005Part013SupportExplicit : Finset ℕ :=
  ([8501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part013 : ℚ :=
  (72267001 : ℚ) / 208844260500000

def SurrogateDiagonalTailChunk000Sub001Block005Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8501
    = surrogateDiagTailX0RatChunk000Sub001Block005Part013

theorem surrogateDiagonalTailChunk000Sub001Block005Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part013] using hcert

def TailChunk000Sub001Block005Part014SupportExplicit : Finset ℕ :=
  ([8502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part014 : ℚ :=
  (401818774625 : ℚ) / 56433482588749824

def SurrogateDiagonalTailChunk000Sub001Block005Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8502
    = surrogateDiagTailX0RatChunk000Sub001Block005Part014

theorem surrogateDiagonalTailChunk000Sub001Block005Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part014] using hcert

def TailChunk000Sub001Block005Part015SupportExplicit : Finset ℕ :=
  ([8503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part015 : ℚ :=
  (3161749085 : ℚ) / 7105359352833024

def SurrogateDiagonalTailChunk000Sub001Block005Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8503
    = surrogateDiagTailX0RatChunk000Sub001Block005Part015

theorem surrogateDiagonalTailChunk000Sub001Block005Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part015] using hcert

def TailChunk000Sub001Block005Part016SupportExplicit : Finset ℕ :=
  ([8506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part016 : ℚ :=
  (282625140625 : ℚ) / 204333649111870752

def SurrogateDiagonalTailChunk000Sub001Block005Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8506
    = surrogateDiagTailX0RatChunk000Sub001Block005Part016

theorem surrogateDiagonalTailChunk000Sub001Block005Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part016] using hcert

def TailChunk000Sub001Block005Part017SupportExplicit : Finset ℕ :=
  ([8507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part017 : ℚ :=
  (87089735621 : ℚ) / 235059713070105600

def SurrogateDiagonalTailChunk000Sub001Block005Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8507
    = surrogateDiagTailX0RatChunk000Sub001Block005Part017

theorem surrogateDiagonalTailChunk000Sub001Block005Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part017] using hcert

def TailChunk000Sub001Block005Part018SupportExplicit : Finset ℕ :=
  ([8509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part018 : ℚ :=
  (14224411175 : ℚ) / 38827020499809696

def SurrogateDiagonalTailChunk000Sub001Block005Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8509
    = surrogateDiagTailX0RatChunk000Sub001Block005Part018

theorem surrogateDiagonalTailChunk000Sub001Block005Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part018] using hcert

def TailChunk000Sub001Block005Part019SupportExplicit : Finset ℕ :=
  ([8510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part019 : ℚ :=
  (446274368975 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub001Block005Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8510
    = surrogateDiagTailX0RatChunk000Sub001Block005Part019

theorem surrogateDiagonalTailChunk000Sub001Block005Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part019] using hcert

def TailChunk000Sub001Block005Part020SupportExplicit : Finset ℕ :=
  ([8511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part020 : ℚ :=
  (1257216005675 : ℚ) / 1294022274040587264

def SurrogateDiagonalTailChunk000Sub001Block005Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8511
    = surrogateDiagTailX0RatChunk000Sub001Block005Part020

theorem surrogateDiagonalTailChunk000Sub001Block005Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part020] using hcert

def TailChunk000Sub001Block005Part021SupportExplicit : Finset ℕ :=
  ([8513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part021 : ℚ :=
  (1132362015625 : ℚ) / 3281658064605806592

def SurrogateDiagonalTailChunk000Sub001Block005Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8513
    = surrogateDiagTailX0RatChunk000Sub001Block005Part021

theorem surrogateDiagonalTailChunk000Sub001Block005Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part021] using hcert

def TailChunk000Sub001Block005Part022SupportExplicit : Finset ℕ :=
  ([8515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part022 : ℚ :=
  (23080578701 : ℚ) / 30328798421975040

def SurrogateDiagonalTailChunk000Sub001Block005Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8515
    = surrogateDiagTailX0RatChunk000Sub001Block005Part022

theorem surrogateDiagonalTailChunk000Sub001Block005Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part022] using hcert

def TailChunk000Sub001Block005Part023SupportExplicit : Finset ℕ :=
  ([8517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part023 : ℚ :=
  (620996979075 : ℚ) / 663648121762349056

def SurrogateDiagonalTailChunk000Sub001Block005Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8517
    = surrogateDiagTailX0RatChunk000Sub001Block005Part023

theorem surrogateDiagonalTailChunk000Sub001Block005Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part023] using hcert

def TailChunk000Sub001Block005Part024SupportExplicit : Finset ℕ :=
  ([8518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block005Part024 : ℚ :=
  (283423140625 : ℚ) / 205489434017679762

def SurrogateDiagonalTailChunk000Sub001Block005Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8518
    = surrogateDiagTailX0RatChunk000Sub001Block005Part024

theorem surrogateDiagonalTailChunk000Sub001Block005Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block005Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block005Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block005Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block005Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block005Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block005HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block005Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block005Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part000
    + surrogateDiagTailX0RatChunk000Sub001Block005Part001
    + surrogateDiagTailX0RatChunk000Sub001Block005Part002
    + surrogateDiagTailX0RatChunk000Sub001Block005Part003
    + surrogateDiagTailX0RatChunk000Sub001Block005Part004
    + surrogateDiagTailX0RatChunk000Sub001Block005Part005
    + surrogateDiagTailX0RatChunk000Sub001Block005Part006
    + surrogateDiagTailX0RatChunk000Sub001Block005Part007
    + surrogateDiagTailX0RatChunk000Sub001Block005Part008
    + surrogateDiagTailX0RatChunk000Sub001Block005Part009

def surrogateDiagonalTailChunk000Sub001Block005MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block005Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block005Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part010
    + surrogateDiagTailX0RatChunk000Sub001Block005Part011
    + surrogateDiagTailX0RatChunk000Sub001Block005Part012
    + surrogateDiagTailX0RatChunk000Sub001Block005Part013
    + surrogateDiagTailX0RatChunk000Sub001Block005Part014
    + surrogateDiagTailX0RatChunk000Sub001Block005Part015
    + surrogateDiagTailX0RatChunk000Sub001Block005Part016
    + surrogateDiagTailX0RatChunk000Sub001Block005Part017
    + surrogateDiagTailX0RatChunk000Sub001Block005Part018
    + surrogateDiagTailX0RatChunk000Sub001Block005Part019

def surrogateDiagonalTailChunk000Sub001Block005TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block005Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block005Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block005Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part020
    + surrogateDiagTailX0RatChunk000Sub001Block005Part021
    + surrogateDiagTailX0RatChunk000Sub001Block005Part022
    + surrogateDiagTailX0RatChunk000Sub001Block005Part023
    + surrogateDiagTailX0RatChunk000Sub001Block005Part024

def surrogateDiagonalTailChunk000Sub001Block005Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block005HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block005MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block005TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block005 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block005Part000
    + surrogateDiagTailX0RatChunk000Sub001Block005Part001
    + surrogateDiagTailX0RatChunk000Sub001Block005Part002
    + surrogateDiagTailX0RatChunk000Sub001Block005Part003
    + surrogateDiagTailX0RatChunk000Sub001Block005Part004
    + surrogateDiagTailX0RatChunk000Sub001Block005Part005
    + surrogateDiagTailX0RatChunk000Sub001Block005Part006
    + surrogateDiagTailX0RatChunk000Sub001Block005Part007
    + surrogateDiagTailX0RatChunk000Sub001Block005Part008
    + surrogateDiagTailX0RatChunk000Sub001Block005Part009
    + surrogateDiagTailX0RatChunk000Sub001Block005Part010
    + surrogateDiagTailX0RatChunk000Sub001Block005Part011
    + surrogateDiagTailX0RatChunk000Sub001Block005Part012
    + surrogateDiagTailX0RatChunk000Sub001Block005Part013
    + surrogateDiagTailX0RatChunk000Sub001Block005Part014
    + surrogateDiagTailX0RatChunk000Sub001Block005Part015
    + surrogateDiagTailX0RatChunk000Sub001Block005Part016
    + surrogateDiagTailX0RatChunk000Sub001Block005Part017
    + surrogateDiagTailX0RatChunk000Sub001Block005Part018
    + surrogateDiagTailX0RatChunk000Sub001Block005Part019
    + surrogateDiagTailX0RatChunk000Sub001Block005Part020
    + surrogateDiagTailX0RatChunk000Sub001Block005Part021
    + surrogateDiagTailX0RatChunk000Sub001Block005Part022
    + surrogateDiagTailX0RatChunk000Sub001Block005Part023
    + surrogateDiagTailX0RatChunk000Sub001Block005Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block005_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block005Head + surrogateDiagTailX0RatChunk000Sub001Block005Mid + surrogateDiagTailX0RatChunk000Sub001Block005Tail =
      surrogateDiagTailX0RatChunk000Sub001Block005 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block005Head surrogateDiagTailX0RatChunk000Sub001Block005Mid surrogateDiagTailX0RatChunk000Sub001Block005Tail surrogateDiagTailX0RatChunk000Sub001Block005
  ring

def SurrogateDiagonalTailChunk000Sub001Block005HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block005HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block005Head

def SurrogateDiagonalTailChunk000Sub001Block005MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block005MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block005Mid

def SurrogateDiagonalTailChunk000Sub001Block005TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block005TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block005Tail

theorem surrogateDiagonalTailChunk000Sub001Block005_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block005HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block005MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block005TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block005Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block005 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block005HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block005MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block005TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block005Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block005_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
