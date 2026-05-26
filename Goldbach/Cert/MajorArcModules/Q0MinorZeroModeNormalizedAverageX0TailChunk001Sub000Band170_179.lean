import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [170,180). -/

/-- Block 170 covers tail-support indices [14250,14275) and q from 23489 to 23529. -/

def TailChunk001Sub000Block170Part000SupportExplicit : Finset ℕ :=
  ([23489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part000 : ℚ :=
  (34534325 : ℚ) / 215283044287897728

def SurrogateDiagonalTailChunk001Sub000Block170Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23489
    = surrogateDiagTailX0RatChunk001Sub000Block170Part000

theorem surrogateDiagonalTailChunk001Sub000Block170Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part000] using hcert

def TailChunk001Sub000Block170Part001SupportExplicit : Finset ℕ :=
  ([23493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part001 : ℚ :=
  (75039882227 : ℚ) / 2669507874816000000

def SurrogateDiagonalTailChunk001Sub000Block170Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23493
    = surrogateDiagTailX0RatChunk001Sub000Block170Part001

theorem surrogateDiagonalTailChunk001Sub000Block170Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part001] using hcert

def TailChunk001Sub000Block170Part002SupportExplicit : Finset ℕ :=
  ([23494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part002 : ℚ :=
  (4260841277 : ℚ) / 742904772172185600

def SurrogateDiagonalTailChunk001Sub000Block170Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23494
    = surrogateDiagTailX0RatChunk001Sub000Block170Part002

theorem surrogateDiagonalTailChunk001Sub000Block170Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part002] using hcert

def TailChunk001Sub000Block170Part003SupportExplicit : Finset ℕ :=
  ([23495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part003 : ℚ :=
  (212514964075 : ℚ) / 38713369055882379264

def SurrogateDiagonalTailChunk001Sub000Block170Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23495
    = surrogateDiagTailX0RatChunk001Sub000Block170Part003

theorem surrogateDiagonalTailChunk001Sub000Block170Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part003] using hcert

def TailChunk001Sub000Block170Part004SupportExplicit : Finset ℕ :=
  ([23497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block170Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23497
    = surrogateDiagTailX0RatChunk001Sub000Block170Part004

theorem surrogateDiagonalTailChunk001Sub000Block170Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part004] using hcert

def TailChunk001Sub000Block170Part005SupportExplicit : Finset ℕ :=
  ([23498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part005 : ℚ :=
  (111265837 : ℚ) / 36755857122284160

def SurrogateDiagonalTailChunk001Sub000Block170Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23498
    = surrogateDiagTailX0RatChunk001Sub000Block170Part005

theorem surrogateDiagonalTailChunk001Sub000Block170Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part005] using hcert

def TailChunk001Sub000Block170Part006SupportExplicit : Finset ℕ :=
  ([23501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part006 : ℚ :=
  (494235853 : ℚ) / 2847965800264200000

def SurrogateDiagonalTailChunk001Sub000Block170Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23501
    = surrogateDiagTailX0RatChunk001Sub000Block170Part006

theorem surrogateDiagonalTailChunk001Sub000Block170Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part006] using hcert

def TailChunk001Sub000Block170Part007SupportExplicit : Finset ℕ :=
  ([23502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part007 : ℚ :=
  (7492703825 : ℚ) / 73503429784887696

def SurrogateDiagonalTailChunk001Sub000Block170Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23502
    = surrogateDiagTailX0RatChunk001Sub000Block170Part007

theorem surrogateDiagonalTailChunk001Sub000Block170Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part007] using hcert

def TailChunk001Sub000Block170Part008SupportExplicit : Finset ℕ :=
  ([23503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part008 : ℚ :=
  (43035288325 : ℚ) / 68068824837769562112

def SurrogateDiagonalTailChunk001Sub000Block170Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23503
    = surrogateDiagTailX0RatChunk001Sub000Block170Part008

theorem surrogateDiagonalTailChunk001Sub000Block170Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part008] using hcert

def TailChunk001Sub000Block170Part009SupportExplicit : Finset ℕ :=
  ([23505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part009 : ℚ :=
  (805273730725 : ℚ) / 15399047067458936832

def SurrogateDiagonalTailChunk001Sub000Block170Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23505
    = surrogateDiagTailX0RatChunk001Sub000Block170Part009

theorem surrogateDiagonalTailChunk001Sub000Block170Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part009] using hcert

def TailChunk001Sub000Block170Part010SupportExplicit : Finset ℕ :=
  ([23506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part010 : ℚ :=
  (645762886525 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk001Sub000Block170Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23506
    = surrogateDiagTailX0RatChunk001Sub000Block170Part010

theorem surrogateDiagonalTailChunk001Sub000Block170Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part010] using hcert

def TailChunk001Sub000Block170Part011SupportExplicit : Finset ℕ :=
  ([23507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part011 : ℚ :=
  (34330120153 : ℚ) / 20820533023966003200

def SurrogateDiagonalTailChunk001Sub000Block170Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23507
    = surrogateDiagTailX0RatChunk001Sub000Block170Part011

theorem surrogateDiagonalTailChunk001Sub000Block170Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part011] using hcert

def TailChunk001Sub000Block170Part012SupportExplicit : Finset ℕ :=
  ([23509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block170Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23509
    = surrogateDiagTailX0RatChunk001Sub000Block170Part012

theorem surrogateDiagonalTailChunk001Sub000Block170Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part012] using hcert

def TailChunk001Sub000Block170Part013SupportExplicit : Finset ℕ :=
  ([23510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part013 : ℚ :=
  (588446687 : ℚ) / 16615002336000000

def SurrogateDiagonalTailChunk001Sub000Block170Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23510
    = surrogateDiagTailX0RatChunk001Sub000Block170Part013

theorem surrogateDiagonalTailChunk001Sub000Block170Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part013] using hcert

def TailChunk001Sub000Block170Part014SupportExplicit : Finset ℕ :=
  ([23511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part014 : ℚ :=
  (4915207461 : ℚ) / 156529729774551040

def SurrogateDiagonalTailChunk001Sub000Block170Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23511
    = surrogateDiagTailX0RatChunk001Sub000Block170Part014

theorem surrogateDiagonalTailChunk001Sub000Block170Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part014] using hcert

def TailChunk001Sub000Block170Part015SupportExplicit : Finset ℕ :=
  ([23513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part015 : ℚ :=
  (705556725575 : ℚ) / 206027233986287306304

def SurrogateDiagonalTailChunk001Sub000Block170Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23513
    = surrogateDiagTailX0RatChunk001Sub000Block170Part015

theorem surrogateDiagonalTailChunk001Sub000Block170Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part015] using hcert

def TailChunk001Sub000Block170Part016SupportExplicit : Finset ℕ :=
  ([23514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part016 : ℚ :=
  (480022669775 : ℚ) / 4713837125392816704

def SurrogateDiagonalTailChunk001Sub000Block170Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23514
    = surrogateDiagTailX0RatChunk001Sub000Block170Part016

theorem surrogateDiagonalTailChunk001Sub000Block170Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part016] using hcert

def TailChunk001Sub000Block170Part017SupportExplicit : Finset ℕ :=
  ([23515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part017 : ℚ :=
  (461016949875 : ℚ) / 104298021152699324416

def SurrogateDiagonalTailChunk001Sub000Block170Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23515
    = surrogateDiagTailX0RatChunk001Sub000Block170Part017

theorem surrogateDiagonalTailChunk001Sub000Block170Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part017] using hcert

def TailChunk001Sub000Block170Part018SupportExplicit : Finset ℕ :=
  ([23518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part018 : ℚ :=
  (239524553 : ℚ) / 21688055233297920

def SurrogateDiagonalTailChunk001Sub000Block170Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23518
    = surrogateDiagTailX0RatChunk001Sub000Block170Part018

theorem surrogateDiagonalTailChunk001Sub000Block170Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part018] using hcert

def TailChunk001Sub000Block170Part019SupportExplicit : Finset ℕ :=
  ([23519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part019 : ℚ :=
  (10180939831 : ℚ) / 26464217128044595200

def SurrogateDiagonalTailChunk001Sub000Block170Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23519
    = surrogateDiagTailX0RatChunk001Sub000Block170Part019

theorem surrogateDiagonalTailChunk001Sub000Block170Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part019] using hcert

def TailChunk001Sub000Block170Part020SupportExplicit : Finset ℕ :=
  ([23521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part020 : ℚ :=
  (73513925 : ℚ) / 281442341182713984

def SurrogateDiagonalTailChunk001Sub000Block170Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23521
    = surrogateDiagTailX0RatChunk001Sub000Block170Part020

theorem surrogateDiagonalTailChunk001Sub000Block170Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part020] using hcert

def TailChunk001Sub000Block170Part021SupportExplicit : Finset ℕ :=
  ([23522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part021 : ℚ :=
  (196316657875 : ℚ) / 38288713971245378688

def SurrogateDiagonalTailChunk001Sub000Block170Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23522
    = surrogateDiagTailX0RatChunk001Sub000Block170Part021

theorem surrogateDiagonalTailChunk001Sub000Block170Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part021] using hcert

def TailChunk001Sub000Block170Part022SupportExplicit : Finset ℕ :=
  ([23523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part022 : ℚ :=
  (1097778569 : ℚ) / 43186006712647680

def SurrogateDiagonalTailChunk001Sub000Block170Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23523
    = surrogateDiagTailX0RatChunk001Sub000Block170Part022

theorem surrogateDiagonalTailChunk001Sub000Block170Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part022] using hcert

def TailChunk001Sub000Block170Part023SupportExplicit : Finset ℕ :=
  ([23527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part023 : ℚ :=
  (28255852307 : ℚ) / 8260740234451353600

def SurrogateDiagonalTailChunk001Sub000Block170Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23527
    = surrogateDiagTailX0RatChunk001Sub000Block170Part023

theorem surrogateDiagonalTailChunk001Sub000Block170Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part023] using hcert

def TailChunk001Sub000Block170Part024SupportExplicit : Finset ℕ :=
  ([23529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block170Part024 : ℚ :=
  (68834777963 : ℚ) / 1518282475776000000

def SurrogateDiagonalTailChunk001Sub000Block170Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23529
    = surrogateDiagTailX0RatChunk001Sub000Block170Part024

theorem surrogateDiagonalTailChunk001Sub000Block170Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block170Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block170Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block170Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block170Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block170Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block170Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block170HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block170Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block170Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block170Part000
    + surrogateDiagTailX0RatChunk001Sub000Block170Part001
    + surrogateDiagTailX0RatChunk001Sub000Block170Part002
    + surrogateDiagTailX0RatChunk001Sub000Block170Part003
    + surrogateDiagTailX0RatChunk001Sub000Block170Part004
    + surrogateDiagTailX0RatChunk001Sub000Block170Part005
    + surrogateDiagTailX0RatChunk001Sub000Block170Part006
    + surrogateDiagTailX0RatChunk001Sub000Block170Part007
    + surrogateDiagTailX0RatChunk001Sub000Block170Part008
    + surrogateDiagTailX0RatChunk001Sub000Block170Part009

def surrogateDiagonalTailChunk001Sub000Block170MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block170Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block170Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block170Part010
    + surrogateDiagTailX0RatChunk001Sub000Block170Part011
    + surrogateDiagTailX0RatChunk001Sub000Block170Part012
    + surrogateDiagTailX0RatChunk001Sub000Block170Part013
    + surrogateDiagTailX0RatChunk001Sub000Block170Part014
    + surrogateDiagTailX0RatChunk001Sub000Block170Part015
    + surrogateDiagTailX0RatChunk001Sub000Block170Part016
    + surrogateDiagTailX0RatChunk001Sub000Block170Part017
    + surrogateDiagTailX0RatChunk001Sub000Block170Part018
    + surrogateDiagTailX0RatChunk001Sub000Block170Part019

def surrogateDiagonalTailChunk001Sub000Block170TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block170Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block170Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block170Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block170Part020
    + surrogateDiagTailX0RatChunk001Sub000Block170Part021
    + surrogateDiagTailX0RatChunk001Sub000Block170Part022
    + surrogateDiagTailX0RatChunk001Sub000Block170Part023
    + surrogateDiagTailX0RatChunk001Sub000Block170Part024

def surrogateDiagonalTailChunk001Sub000Block170Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block170HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block170MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block170TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block170 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block170Part000
    + surrogateDiagTailX0RatChunk001Sub000Block170Part001
    + surrogateDiagTailX0RatChunk001Sub000Block170Part002
    + surrogateDiagTailX0RatChunk001Sub000Block170Part003
    + surrogateDiagTailX0RatChunk001Sub000Block170Part004
    + surrogateDiagTailX0RatChunk001Sub000Block170Part005
    + surrogateDiagTailX0RatChunk001Sub000Block170Part006
    + surrogateDiagTailX0RatChunk001Sub000Block170Part007
    + surrogateDiagTailX0RatChunk001Sub000Block170Part008
    + surrogateDiagTailX0RatChunk001Sub000Block170Part009
    + surrogateDiagTailX0RatChunk001Sub000Block170Part010
    + surrogateDiagTailX0RatChunk001Sub000Block170Part011
    + surrogateDiagTailX0RatChunk001Sub000Block170Part012
    + surrogateDiagTailX0RatChunk001Sub000Block170Part013
    + surrogateDiagTailX0RatChunk001Sub000Block170Part014
    + surrogateDiagTailX0RatChunk001Sub000Block170Part015
    + surrogateDiagTailX0RatChunk001Sub000Block170Part016
    + surrogateDiagTailX0RatChunk001Sub000Block170Part017
    + surrogateDiagTailX0RatChunk001Sub000Block170Part018
    + surrogateDiagTailX0RatChunk001Sub000Block170Part019
    + surrogateDiagTailX0RatChunk001Sub000Block170Part020
    + surrogateDiagTailX0RatChunk001Sub000Block170Part021
    + surrogateDiagTailX0RatChunk001Sub000Block170Part022
    + surrogateDiagTailX0RatChunk001Sub000Block170Part023
    + surrogateDiagTailX0RatChunk001Sub000Block170Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block170_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block170Head + surrogateDiagTailX0RatChunk001Sub000Block170Mid + surrogateDiagTailX0RatChunk001Sub000Block170Tail =
      surrogateDiagTailX0RatChunk001Sub000Block170 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block170Head surrogateDiagTailX0RatChunk001Sub000Block170Mid surrogateDiagTailX0RatChunk001Sub000Block170Tail surrogateDiagTailX0RatChunk001Sub000Block170
  ring

def SurrogateDiagonalTailChunk001Sub000Block170HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block170HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block170Head

def SurrogateDiagonalTailChunk001Sub000Block170MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block170MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block170Mid

def SurrogateDiagonalTailChunk001Sub000Block170TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block170TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block170Tail

theorem surrogateDiagonalTailChunk001Sub000Block170_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block170HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block170MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block170TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block170Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block170 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block170HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block170MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block170TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block170Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block170_eq_head_add_mid_add_tail

/-- Block 171 covers tail-support indices [14275,14300) and q from 23530 to 23570. -/

def TailChunk001Sub000Block171Part000SupportExplicit : Finset ℕ :=
  ([23530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part000 : ℚ :=
  (925483963 : ℚ) / 15482436924211200

def SurrogateDiagonalTailChunk001Sub000Block171Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23530
    = surrogateDiagTailX0RatChunk001Sub000Block171Part000

theorem surrogateDiagonalTailChunk001Sub000Block171Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part000] using hcert

def TailChunk001Sub000Block171Part001SupportExplicit : Finset ℕ :=
  ([23531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23531
    = surrogateDiagTailX0RatChunk001Sub000Block171Part001

theorem surrogateDiagonalTailChunk001Sub000Block171Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part001] using hcert

def TailChunk001Sub000Block171Part002SupportExplicit : Finset ℕ :=
  ([23533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part002 : ℚ :=
  (350841393 : ℚ) / 2414668650496000000

def SurrogateDiagonalTailChunk001Sub000Block171Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23533
    = surrogateDiagTailX0RatChunk001Sub000Block171Part002

theorem surrogateDiagonalTailChunk001Sub000Block171Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part002] using hcert

def TailChunk001Sub000Block171Part003SupportExplicit : Finset ℕ :=
  ([23537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23537
    = surrogateDiagTailX0RatChunk001Sub000Block171Part003

theorem surrogateDiagonalTailChunk001Sub000Block171Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part003] using hcert

def TailChunk001Sub000Block171Part004SupportExplicit : Finset ℕ :=
  ([23538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part004 : ℚ :=
  (481002669725 : ℚ) / 4733116597693852224

def SurrogateDiagonalTailChunk001Sub000Block171Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23538
    = surrogateDiagTailX0RatChunk001Sub000Block171Part004

theorem surrogateDiagonalTailChunk001Sub000Block171Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part004] using hcert

def TailChunk001Sub000Block171Part005SupportExplicit : Finset ℕ :=
  ([23539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23539
    = surrogateDiagTailX0RatChunk001Sub000Block171Part005

theorem surrogateDiagonalTailChunk001Sub000Block171Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part005] using hcert

def TailChunk001Sub000Block171Part006SupportExplicit : Finset ℕ :=
  ([23541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part006 : ℚ :=
  (555535567225 : ℚ) / 10266031378305957888

def SurrogateDiagonalTailChunk001Sub000Block171Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23541
    = surrogateDiagTailX0RatChunk001Sub000Block171Part006

theorem surrogateDiagonalTailChunk001Sub000Block171Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part006] using hcert

def TailChunk001Sub000Block171Part007SupportExplicit : Finset ℕ :=
  ([23542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part007 : ℚ :=
  (119095675 : ℚ) / 75011944651772544

def SurrogateDiagonalTailChunk001Sub000Block171Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23542
    = surrogateDiagTailX0RatChunk001Sub000Block171Part007

theorem surrogateDiagonalTailChunk001Sub000Block171Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part007] using hcert

def TailChunk001Sub000Block171Part008SupportExplicit : Finset ℕ :=
  ([23543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part008 : ℚ :=
  (16527367189 : ℚ) / 22260049916815411200

def SurrogateDiagonalTailChunk001Sub000Block171Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23543
    = surrogateDiagTailX0RatChunk001Sub000Block171Part008

theorem surrogateDiagonalTailChunk001Sub000Block171Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part008] using hcert

def TailChunk001Sub000Block171Part009SupportExplicit : Finset ℕ :=
  ([23545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part009 : ℚ :=
  (18939962875 : ℚ) / 3005370811671379968

def SurrogateDiagonalTailChunk001Sub000Block171Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23545
    = surrogateDiagTailX0RatChunk001Sub000Block171Part009

theorem surrogateDiagonalTailChunk001Sub000Block171Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part009] using hcert

def TailChunk001Sub000Block171Part010SupportExplicit : Finset ℕ :=
  ([23546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part010 : ℚ :=
  (58044937 : ℚ) / 32621430885580800

def SurrogateDiagonalTailChunk001Sub000Block171Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23546
    = surrogateDiagTailX0RatChunk001Sub000Block171Part010

theorem surrogateDiagonalTailChunk001Sub000Block171Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part010] using hcert

def TailChunk001Sub000Block171Part011SupportExplicit : Finset ℕ :=
  ([23547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part011 : ℚ :=
  (1883721044675 : ℚ) / 68011213638463448064

def SurrogateDiagonalTailChunk001Sub000Block171Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23547
    = surrogateDiagTailX0RatChunk001Sub000Block171Part011

theorem surrogateDiagonalTailChunk001Sub000Block171Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part011] using hcert

def TailChunk001Sub000Block171Part012SupportExplicit : Finset ℕ :=
  ([23549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23549
    = surrogateDiagTailX0RatChunk001Sub000Block171Part012

theorem surrogateDiagonalTailChunk001Sub000Block171Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part012] using hcert

def TailChunk001Sub000Block171Part013SupportExplicit : Finset ℕ :=
  ([23551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part013 : ℚ :=
  (5754632431 : ℚ) / 5244232676808000000

def SurrogateDiagonalTailChunk001Sub000Block171Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23551
    = surrogateDiagTailX0RatChunk001Sub000Block171Part013

theorem surrogateDiagonalTailChunk001Sub000Block171Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part013] using hcert

def TailChunk001Sub000Block171Part014SupportExplicit : Finset ℕ :=
  ([23554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23554
    = surrogateDiagTailX0RatChunk001Sub000Block171Part014

theorem surrogateDiagonalTailChunk001Sub000Block171Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part014] using hcert

def TailChunk001Sub000Block171Part015SupportExplicit : Finset ℕ :=
  ([23555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part015 : ℚ :=
  (172317252125 : ℚ) / 14098330000130310144

def SurrogateDiagonalTailChunk001Sub000Block171Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23555
    = surrogateDiagTailX0RatChunk001Sub000Block171Part015

theorem surrogateDiagonalTailChunk001Sub000Block171Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part015] using hcert

def TailChunk001Sub000Block171Part016SupportExplicit : Finset ℕ :=
  ([23557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23557
    = surrogateDiagTailX0RatChunk001Sub000Block171Part016

theorem surrogateDiagonalTailChunk001Sub000Block171Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part016] using hcert

def TailChunk001Sub000Block171Part017SupportExplicit : Finset ℕ :=
  ([23558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23558
    = surrogateDiagTailX0RatChunk001Sub000Block171Part017

theorem surrogateDiagonalTailChunk001Sub000Block171Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part017] using hcert

def TailChunk001Sub000Block171Part018SupportExplicit : Finset ℕ :=
  ([23559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part018 : ℚ :=
  (120437312225 : ℚ) / 4752455149021130304

def SurrogateDiagonalTailChunk001Sub000Block171Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23559
    = surrogateDiagTailX0RatChunk001Sub000Block171Part018

theorem surrogateDiagonalTailChunk001Sub000Block171Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part018] using hcert

def TailChunk001Sub000Block171Part019SupportExplicit : Finset ℕ :=
  ([23561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23561
    = surrogateDiagTailX0RatChunk001Sub000Block171Part019

theorem surrogateDiagonalTailChunk001Sub000Block171Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part019] using hcert

def TailChunk001Sub000Block171Part020SupportExplicit : Finset ℕ :=
  ([23563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23563
    = surrogateDiagTailX0RatChunk001Sub000Block171Part020

theorem surrogateDiagonalTailChunk001Sub000Block171Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part020] using hcert

def TailChunk001Sub000Block171Part021SupportExplicit : Finset ℕ :=
  ([23565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part021 : ℚ :=
  (5395930497 : ℚ) / 103713231469260800

def SurrogateDiagonalTailChunk001Sub000Block171Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23565
    = surrogateDiagTailX0RatChunk001Sub000Block171Part021

theorem surrogateDiagonalTailChunk001Sub000Block171Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part021] using hcert

def TailChunk001Sub000Block171Part022SupportExplicit : Finset ℕ :=
  ([23566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23566
    = surrogateDiagTailX0RatChunk001Sub000Block171Part022

theorem surrogateDiagonalTailChunk001Sub000Block171Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part022] using hcert

def TailChunk001Sub000Block171Part023SupportExplicit : Finset ℕ :=
  ([23567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block171Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23567
    = surrogateDiagTailX0RatChunk001Sub000Block171Part023

theorem surrogateDiagonalTailChunk001Sub000Block171Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part023] using hcert

def TailChunk001Sub000Block171Part024SupportExplicit : Finset ℕ :=
  ([23570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block171Part024 : ℚ :=
  (694953649525 : ℚ) / 19722772656463577088

def SurrogateDiagonalTailChunk001Sub000Block171Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23570
    = surrogateDiagTailX0RatChunk001Sub000Block171Part024

theorem surrogateDiagonalTailChunk001Sub000Block171Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block171Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block171Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block171Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block171Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block171Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block171HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block171Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block171Part000
    + surrogateDiagTailX0RatChunk001Sub000Block171Part001
    + surrogateDiagTailX0RatChunk001Sub000Block171Part002
    + surrogateDiagTailX0RatChunk001Sub000Block171Part003
    + surrogateDiagTailX0RatChunk001Sub000Block171Part004
    + surrogateDiagTailX0RatChunk001Sub000Block171Part005
    + surrogateDiagTailX0RatChunk001Sub000Block171Part006
    + surrogateDiagTailX0RatChunk001Sub000Block171Part007
    + surrogateDiagTailX0RatChunk001Sub000Block171Part008
    + surrogateDiagTailX0RatChunk001Sub000Block171Part009

def surrogateDiagonalTailChunk001Sub000Block171MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block171Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block171Part010
    + surrogateDiagTailX0RatChunk001Sub000Block171Part011
    + surrogateDiagTailX0RatChunk001Sub000Block171Part012
    + surrogateDiagTailX0RatChunk001Sub000Block171Part013
    + surrogateDiagTailX0RatChunk001Sub000Block171Part014
    + surrogateDiagTailX0RatChunk001Sub000Block171Part015
    + surrogateDiagTailX0RatChunk001Sub000Block171Part016
    + surrogateDiagTailX0RatChunk001Sub000Block171Part017
    + surrogateDiagTailX0RatChunk001Sub000Block171Part018
    + surrogateDiagTailX0RatChunk001Sub000Block171Part019

def surrogateDiagonalTailChunk001Sub000Block171TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block171Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block171Part020
    + surrogateDiagTailX0RatChunk001Sub000Block171Part021
    + surrogateDiagTailX0RatChunk001Sub000Block171Part022
    + surrogateDiagTailX0RatChunk001Sub000Block171Part023
    + surrogateDiagTailX0RatChunk001Sub000Block171Part024

def surrogateDiagonalTailChunk001Sub000Block171Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block171HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block171MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block171TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block171 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block171Part000
    + surrogateDiagTailX0RatChunk001Sub000Block171Part001
    + surrogateDiagTailX0RatChunk001Sub000Block171Part002
    + surrogateDiagTailX0RatChunk001Sub000Block171Part003
    + surrogateDiagTailX0RatChunk001Sub000Block171Part004
    + surrogateDiagTailX0RatChunk001Sub000Block171Part005
    + surrogateDiagTailX0RatChunk001Sub000Block171Part006
    + surrogateDiagTailX0RatChunk001Sub000Block171Part007
    + surrogateDiagTailX0RatChunk001Sub000Block171Part008
    + surrogateDiagTailX0RatChunk001Sub000Block171Part009
    + surrogateDiagTailX0RatChunk001Sub000Block171Part010
    + surrogateDiagTailX0RatChunk001Sub000Block171Part011
    + surrogateDiagTailX0RatChunk001Sub000Block171Part012
    + surrogateDiagTailX0RatChunk001Sub000Block171Part013
    + surrogateDiagTailX0RatChunk001Sub000Block171Part014
    + surrogateDiagTailX0RatChunk001Sub000Block171Part015
    + surrogateDiagTailX0RatChunk001Sub000Block171Part016
    + surrogateDiagTailX0RatChunk001Sub000Block171Part017
    + surrogateDiagTailX0RatChunk001Sub000Block171Part018
    + surrogateDiagTailX0RatChunk001Sub000Block171Part019
    + surrogateDiagTailX0RatChunk001Sub000Block171Part020
    + surrogateDiagTailX0RatChunk001Sub000Block171Part021
    + surrogateDiagTailX0RatChunk001Sub000Block171Part022
    + surrogateDiagTailX0RatChunk001Sub000Block171Part023
    + surrogateDiagTailX0RatChunk001Sub000Block171Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block171_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block171Head + surrogateDiagTailX0RatChunk001Sub000Block171Mid + surrogateDiagTailX0RatChunk001Sub000Block171Tail =
      surrogateDiagTailX0RatChunk001Sub000Block171 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block171Head surrogateDiagTailX0RatChunk001Sub000Block171Mid surrogateDiagTailX0RatChunk001Sub000Block171Tail surrogateDiagTailX0RatChunk001Sub000Block171
  ring

def SurrogateDiagonalTailChunk001Sub000Block171HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block171HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block171Head

def SurrogateDiagonalTailChunk001Sub000Block171MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block171MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block171Mid

def SurrogateDiagonalTailChunk001Sub000Block171TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block171TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block171Tail

theorem surrogateDiagonalTailChunk001Sub000Block171_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block171HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block171MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block171TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block171Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block171 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block171HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block171MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block171TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block171Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block171_eq_head_add_mid_add_tail

/-- Block 172 covers tail-support indices [14300,14325) and q from 23573 to 23611. -/

def TailChunk001Sub000Block172Part000SupportExplicit : Finset ℕ :=
  ([23573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part000 : ℚ :=
  (480444607 : ℚ) / 438655398764045400

def SurrogateDiagonalTailChunk001Sub000Block172Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23573
    = surrogateDiagTailX0RatChunk001Sub000Block172Part000

theorem surrogateDiagonalTailChunk001Sub000Block172Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part000] using hcert

def TailChunk001Sub000Block172Part001SupportExplicit : Finset ℕ :=
  ([23574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part001 : ℚ :=
  (241237272325 : ℚ) / 2381073308496371712

def SurrogateDiagonalTailChunk001Sub000Block172Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23574
    = surrogateDiagTailX0RatChunk001Sub000Block172Part001

theorem surrogateDiagonalTailChunk001Sub000Block172Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part001] using hcert

def TailChunk001Sub000Block172Part002SupportExplicit : Finset ℕ :=
  ([23577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part002 : ℚ :=
  (520682177 : ℚ) / 18151040554214400

def SurrogateDiagonalTailChunk001Sub000Block172Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23577
    = surrogateDiagTailX0RatChunk001Sub000Block172Part002

theorem surrogateDiagonalTailChunk001Sub000Block172Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part002] using hcert

def TailChunk001Sub000Block172Part003SupportExplicit : Finset ℕ :=
  ([23578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23578
    = surrogateDiagTailX0RatChunk001Sub000Block172Part003

theorem surrogateDiagonalTailChunk001Sub000Block172Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part003] using hcert

def TailChunk001Sub000Block172Part004SupportExplicit : Finset ℕ :=
  ([23579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part004 : ℚ :=
  (215851803175 : ℚ) / 115575772341759639552

def SurrogateDiagonalTailChunk001Sub000Block172Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23579
    = surrogateDiagTailX0RatChunk001Sub000Block172Part004

theorem surrogateDiagonalTailChunk001Sub000Block172Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part004] using hcert

def TailChunk001Sub000Block172Part005SupportExplicit : Finset ℕ :=
  ([23581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23581
    = surrogateDiagTailX0RatChunk001Sub000Block172Part005

theorem surrogateDiagonalTailChunk001Sub000Block172Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part005] using hcert

def TailChunk001Sub000Block172Part006SupportExplicit : Finset ℕ :=
  ([23582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part006 : ℚ :=
  (28895439875 : ℚ) / 3881701401084168192

def SurrogateDiagonalTailChunk001Sub000Block172Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23582
    = surrogateDiagTailX0RatChunk001Sub000Block172Part006

theorem surrogateDiagonalTailChunk001Sub000Block172Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part006] using hcert

def TailChunk001Sub000Block172Part007SupportExplicit : Finset ℕ :=
  ([23583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part007 : ℚ :=
  (91900302925 : ℚ) / 2282552471867171328

def SurrogateDiagonalTailChunk001Sub000Block172Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23583
    = surrogateDiagTailX0RatChunk001Sub000Block172Part007

theorem surrogateDiagonalTailChunk001Sub000Block172Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part007] using hcert

def TailChunk001Sub000Block172Part008SupportExplicit : Finset ℕ :=
  ([23585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part008 : ℚ :=
  (232377942975 : ℚ) / 23389968734611308544

def SurrogateDiagonalTailChunk001Sub000Block172Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23585
    = surrogateDiagTailX0RatChunk001Sub000Block172Part008

theorem surrogateDiagonalTailChunk001Sub000Block172Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part008] using hcert

def TailChunk001Sub000Block172Part009SupportExplicit : Finset ℕ :=
  ([23586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part009 : ℚ :=
  (3863725357 : ℚ) / 38174823199552320

def SurrogateDiagonalTailChunk001Sub000Block172Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23586
    = surrogateDiagTailX0RatChunk001Sub000Block172Part009

theorem surrogateDiagonalTailChunk001Sub000Block172Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part009] using hcert

def TailChunk001Sub000Block172Part010SupportExplicit : Finset ℕ :=
  ([23587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part010 : ℚ :=
  (102708657625 : ℚ) / 731420172440629659648

def SurrogateDiagonalTailChunk001Sub000Block172Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23587
    = surrogateDiagTailX0RatChunk001Sub000Block172Part010

theorem surrogateDiagonalTailChunk001Sub000Block172Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part010] using hcert

def TailChunk001Sub000Block172Part011SupportExplicit : Finset ℕ :=
  ([23590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part011 : ℚ :=
  (65074584275 : ℚ) / 587430416672096256

def SurrogateDiagonalTailChunk001Sub000Block172Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23590
    = surrogateDiagTailX0RatChunk001Sub000Block172Part011

theorem surrogateDiagonalTailChunk001Sub000Block172Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part011] using hcert

def TailChunk001Sub000Block172Part012SupportExplicit : Finset ℕ :=
  ([23591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part012 : ℚ :=
  (9029764099 : ℚ) / 27028767232512000000

def SurrogateDiagonalTailChunk001Sub000Block172Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23591
    = surrogateDiagTailX0RatChunk001Sub000Block172Part012

theorem surrogateDiagonalTailChunk001Sub000Block172Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part012] using hcert

def TailChunk001Sub000Block172Part013SupportExplicit : Finset ℕ :=
  ([23593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23593
    = surrogateDiagTailX0RatChunk001Sub000Block172Part013

theorem surrogateDiagonalTailChunk001Sub000Block172Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part013] using hcert

def TailChunk001Sub000Block172Part014SupportExplicit : Finset ℕ :=
  ([23594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part014 : ℚ :=
  (1765553543 : ℚ) / 874678025625000000

def SurrogateDiagonalTailChunk001Sub000Block172Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23594
    = surrogateDiagTailX0RatChunk001Sub000Block172Part014

theorem surrogateDiagonalTailChunk001Sub000Block172Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part014] using hcert

def TailChunk001Sub000Block172Part015SupportExplicit : Finset ℕ :=
  ([23597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part015 : ℚ :=
  (28467246733 : ℚ) / 16719044558539651200

def SurrogateDiagonalTailChunk001Sub000Block172Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23597
    = surrogateDiagTailX0RatChunk001Sub000Block172Part015

theorem surrogateDiagonalTailChunk001Sub000Block172Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part015] using hcert

def TailChunk001Sub000Block172Part016SupportExplicit : Finset ℕ :=
  ([23599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23599
    = surrogateDiagTailX0RatChunk001Sub000Block172Part016

theorem surrogateDiagonalTailChunk001Sub000Block172Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part016] using hcert

def TailChunk001Sub000Block172Part017SupportExplicit : Finset ℕ :=
  ([23601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part017 : ℚ :=
  (1933873620425 : ℚ) / 76583042167523079744

def SurrogateDiagonalTailChunk001Sub000Block172Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23601
    = surrogateDiagTailX0RatChunk001Sub000Block172Part017

theorem surrogateDiagonalTailChunk001Sub000Block172Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part017] using hcert

def TailChunk001Sub000Block172Part018SupportExplicit : Finset ℕ :=
  ([23602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23602
    = surrogateDiagTailX0RatChunk001Sub000Block172Part018

theorem surrogateDiagonalTailChunk001Sub000Block172Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part018] using hcert

def TailChunk001Sub000Block172Part019SupportExplicit : Finset ℕ :=
  ([23603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23603
    = surrogateDiagTailX0RatChunk001Sub000Block172Part019

theorem surrogateDiagonalTailChunk001Sub000Block172Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part019] using hcert

def TailChunk001Sub000Block172Part020SupportExplicit : Finset ℕ :=
  ([23605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part020 : ℚ :=
  (3716401593 : ℚ) / 847234341514772480

def SurrogateDiagonalTailChunk001Sub000Block172Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23605
    = surrogateDiagTailX0RatChunk001Sub000Block172Part020

theorem surrogateDiagonalTailChunk001Sub000Block172Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part020] using hcert

def TailChunk001Sub000Block172Part021SupportExplicit : Finset ℕ :=
  ([23606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part021 : ℚ :=
  (5127554281 : ℚ) / 258148132326604800

def SurrogateDiagonalTailChunk001Sub000Block172Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23606
    = surrogateDiagTailX0RatChunk001Sub000Block172Part021

theorem surrogateDiagonalTailChunk001Sub000Block172Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part021] using hcert

def TailChunk001Sub000Block172Part022SupportExplicit : Finset ℕ :=
  ([23609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block172Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23609
    = surrogateDiagTailX0RatChunk001Sub000Block172Part022

theorem surrogateDiagonalTailChunk001Sub000Block172Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part022] using hcert

def TailChunk001Sub000Block172Part023SupportExplicit : Finset ℕ :=
  ([23610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part023 : ℚ :=
  (1045045623025 : ℚ) / 3909101895634157568

def SurrogateDiagonalTailChunk001Sub000Block172Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23610
    = surrogateDiagTailX0RatChunk001Sub000Block172Part023

theorem surrogateDiagonalTailChunk001Sub000Block172Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part023] using hcert

def TailChunk001Sub000Block172Part024SupportExplicit : Finset ℕ :=
  ([23611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block172Part024 : ℚ :=
  (712523918425 : ℚ) / 418969225765892671488

def SurrogateDiagonalTailChunk001Sub000Block172Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23611
    = surrogateDiagTailX0RatChunk001Sub000Block172Part024

theorem surrogateDiagonalTailChunk001Sub000Block172Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block172Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block172Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block172Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block172Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block172Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block172HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block172Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block172Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block172Part000
    + surrogateDiagTailX0RatChunk001Sub000Block172Part001
    + surrogateDiagTailX0RatChunk001Sub000Block172Part002
    + surrogateDiagTailX0RatChunk001Sub000Block172Part003
    + surrogateDiagTailX0RatChunk001Sub000Block172Part004
    + surrogateDiagTailX0RatChunk001Sub000Block172Part005
    + surrogateDiagTailX0RatChunk001Sub000Block172Part006
    + surrogateDiagTailX0RatChunk001Sub000Block172Part007
    + surrogateDiagTailX0RatChunk001Sub000Block172Part008
    + surrogateDiagTailX0RatChunk001Sub000Block172Part009

def surrogateDiagonalTailChunk001Sub000Block172MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block172Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block172Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block172Part010
    + surrogateDiagTailX0RatChunk001Sub000Block172Part011
    + surrogateDiagTailX0RatChunk001Sub000Block172Part012
    + surrogateDiagTailX0RatChunk001Sub000Block172Part013
    + surrogateDiagTailX0RatChunk001Sub000Block172Part014
    + surrogateDiagTailX0RatChunk001Sub000Block172Part015
    + surrogateDiagTailX0RatChunk001Sub000Block172Part016
    + surrogateDiagTailX0RatChunk001Sub000Block172Part017
    + surrogateDiagTailX0RatChunk001Sub000Block172Part018
    + surrogateDiagTailX0RatChunk001Sub000Block172Part019

def surrogateDiagonalTailChunk001Sub000Block172TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block172Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block172Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block172Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block172Part020
    + surrogateDiagTailX0RatChunk001Sub000Block172Part021
    + surrogateDiagTailX0RatChunk001Sub000Block172Part022
    + surrogateDiagTailX0RatChunk001Sub000Block172Part023
    + surrogateDiagTailX0RatChunk001Sub000Block172Part024

def surrogateDiagonalTailChunk001Sub000Block172Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block172HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block172MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block172TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block172 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block172Part000
    + surrogateDiagTailX0RatChunk001Sub000Block172Part001
    + surrogateDiagTailX0RatChunk001Sub000Block172Part002
    + surrogateDiagTailX0RatChunk001Sub000Block172Part003
    + surrogateDiagTailX0RatChunk001Sub000Block172Part004
    + surrogateDiagTailX0RatChunk001Sub000Block172Part005
    + surrogateDiagTailX0RatChunk001Sub000Block172Part006
    + surrogateDiagTailX0RatChunk001Sub000Block172Part007
    + surrogateDiagTailX0RatChunk001Sub000Block172Part008
    + surrogateDiagTailX0RatChunk001Sub000Block172Part009
    + surrogateDiagTailX0RatChunk001Sub000Block172Part010
    + surrogateDiagTailX0RatChunk001Sub000Block172Part011
    + surrogateDiagTailX0RatChunk001Sub000Block172Part012
    + surrogateDiagTailX0RatChunk001Sub000Block172Part013
    + surrogateDiagTailX0RatChunk001Sub000Block172Part014
    + surrogateDiagTailX0RatChunk001Sub000Block172Part015
    + surrogateDiagTailX0RatChunk001Sub000Block172Part016
    + surrogateDiagTailX0RatChunk001Sub000Block172Part017
    + surrogateDiagTailX0RatChunk001Sub000Block172Part018
    + surrogateDiagTailX0RatChunk001Sub000Block172Part019
    + surrogateDiagTailX0RatChunk001Sub000Block172Part020
    + surrogateDiagTailX0RatChunk001Sub000Block172Part021
    + surrogateDiagTailX0RatChunk001Sub000Block172Part022
    + surrogateDiagTailX0RatChunk001Sub000Block172Part023
    + surrogateDiagTailX0RatChunk001Sub000Block172Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block172_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block172Head + surrogateDiagTailX0RatChunk001Sub000Block172Mid + surrogateDiagTailX0RatChunk001Sub000Block172Tail =
      surrogateDiagTailX0RatChunk001Sub000Block172 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block172Head surrogateDiagTailX0RatChunk001Sub000Block172Mid surrogateDiagTailX0RatChunk001Sub000Block172Tail surrogateDiagTailX0RatChunk001Sub000Block172
  ring

def SurrogateDiagonalTailChunk001Sub000Block172HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block172HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block172Head

def SurrogateDiagonalTailChunk001Sub000Block172MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block172MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block172Mid

def SurrogateDiagonalTailChunk001Sub000Block172TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block172TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block172Tail

theorem surrogateDiagonalTailChunk001Sub000Block172_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block172HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block172MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block172TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block172Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block172 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block172HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block172MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block172TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block172Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block172_eq_head_add_mid_add_tail

/-- Block 173 covers tail-support indices [14325,14350) and q from 23613 to 23651. -/

def TailChunk001Sub000Block173Part000SupportExplicit : Finset ℕ :=
  ([23613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part000 : ℚ :=
  (619740669875 : ℚ) / 19908723913185558528

def SurrogateDiagonalTailChunk001Sub000Block173Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23613
    = surrogateDiagTailX0RatChunk001Sub000Block173Part000

theorem surrogateDiagonalTailChunk001Sub000Block173Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part000] using hcert

def TailChunk001Sub000Block173Part001SupportExplicit : Finset ℕ :=
  ([23614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23614
    = surrogateDiagTailX0RatChunk001Sub000Block173Part001

theorem surrogateDiagonalTailChunk001Sub000Block173Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part001] using hcert

def TailChunk001Sub000Block173Part002SupportExplicit : Finset ℕ :=
  ([23615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part002 : ℚ :=
  (1394830847125 : ℚ) / 318251716832903251968

def SurrogateDiagonalTailChunk001Sub000Block173Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23615
    = surrogateDiagTailX0RatChunk001Sub000Block173Part002

theorem surrogateDiagonalTailChunk001Sub000Block173Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part002] using hcert

def TailChunk001Sub000Block173Part003SupportExplicit : Finset ℕ :=
  ([23617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part003 : ℚ :=
  (1451854991 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk001Sub000Block173Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23617
    = surrogateDiagTailX0RatChunk001Sub000Block173Part003

theorem surrogateDiagonalTailChunk001Sub000Block173Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part003] using hcert

def TailChunk001Sub000Block173Part004SupportExplicit : Finset ℕ :=
  ([23619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part004 : ℚ :=
  (968412247675 : ℚ) / 38408486316945702912

def SurrogateDiagonalTailChunk001Sub000Block173Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23619
    = surrogateDiagTailX0RatChunk001Sub000Block173Part004

theorem surrogateDiagonalTailChunk001Sub000Block173Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part004] using hcert

def TailChunk001Sub000Block173Part005SupportExplicit : Finset ℕ :=
  ([23621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part005 : ℚ :=
  (742408377025 : ℚ) / 449594486917338267648

def SurrogateDiagonalTailChunk001Sub000Block173Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23621
    = surrogateDiagTailX0RatChunk001Sub000Block173Part005

theorem surrogateDiagonalTailChunk001Sub000Block173Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part005] using hcert

def TailChunk001Sub000Block173Part006SupportExplicit : Finset ℕ :=
  ([23622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part006 : ℚ :=
  (1129304789 : ℚ) / 9334820856453120

def SurrogateDiagonalTailChunk001Sub000Block173Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23622
    = surrogateDiagTailX0RatChunk001Sub000Block173Part006

theorem surrogateDiagonalTailChunk001Sub000Block173Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part006] using hcert

def TailChunk001Sub000Block173Part007SupportExplicit : Finset ℕ :=
  ([23623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23623
    = surrogateDiagTailX0RatChunk001Sub000Block173Part007

theorem surrogateDiagonalTailChunk001Sub000Block173Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part007] using hcert

def TailChunk001Sub000Block173Part008SupportExplicit : Finset ℕ :=
  ([23626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23626
    = surrogateDiagTailX0RatChunk001Sub000Block173Part008

theorem surrogateDiagonalTailChunk001Sub000Block173Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part008] using hcert

def TailChunk001Sub000Block173Part009SupportExplicit : Finset ℕ :=
  ([23627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23627
    = surrogateDiagTailX0RatChunk001Sub000Block173Part009

theorem surrogateDiagonalTailChunk001Sub000Block173Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part009] using hcert

def TailChunk001Sub000Block173Part010SupportExplicit : Finset ℕ :=
  ([23629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23629
    = surrogateDiagTailX0RatChunk001Sub000Block173Part010

theorem surrogateDiagonalTailChunk001Sub000Block173Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part010] using hcert

def TailChunk001Sub000Block173Part011SupportExplicit : Finset ℕ :=
  ([23630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part011 : ℚ :=
  (794747845675 : ℚ) / 15214689734086361088

def SurrogateDiagonalTailChunk001Sub000Block173Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23630
    = surrogateDiagTailX0RatChunk001Sub000Block173Part011

theorem surrogateDiagonalTailChunk001Sub000Block173Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part011] using hcert

def TailChunk001Sub000Block173Part012SupportExplicit : Finset ℕ :=
  ([23631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part012 : ℚ :=
  (484698248825 : ℚ) / 19243305933875333376

def SurrogateDiagonalTailChunk001Sub000Block173Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23631
    = surrogateDiagTailX0RatChunk001Sub000Block173Part012

theorem surrogateDiagonalTailChunk001Sub000Block173Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part012] using hcert

def TailChunk001Sub000Block173Part013SupportExplicit : Finset ℕ :=
  ([23633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23633
    = surrogateDiagTailX0RatChunk001Sub000Block173Part013

theorem surrogateDiagonalTailChunk001Sub000Block173Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part013] using hcert

def TailChunk001Sub000Block173Part014SupportExplicit : Finset ℕ :=
  ([23635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part014 : ℚ :=
  (1517405996125 : ℚ) / 270993583391176654848

def SurrogateDiagonalTailChunk001Sub000Block173Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23635
    = surrogateDiagTailX0RatChunk001Sub000Block173Part014

theorem surrogateDiagonalTailChunk001Sub000Block173Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part014] using hcert

def TailChunk001Sub000Block173Part015SupportExplicit : Finset ℕ :=
  ([23637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part015 : ℚ :=
  (1939777620275 : ℚ) / 77051438614230709824

def SurrogateDiagonalTailChunk001Sub000Block173Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23637
    = surrogateDiagTailX0RatChunk001Sub000Block173Part015

theorem surrogateDiagonalTailChunk001Sub000Block173Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part015] using hcert

def TailChunk001Sub000Block173Part016SupportExplicit : Finset ℕ :=
  ([23638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part016 : ℚ :=
  (41918765075 : ℚ) / 22203535616924673024

def SurrogateDiagonalTailChunk001Sub000Block173Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23638
    = surrogateDiagTailX0RatChunk001Sub000Block173Part016

theorem surrogateDiagonalTailChunk001Sub000Block173Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part016] using hcert

def TailChunk001Sub000Block173Part017SupportExplicit : Finset ℕ :=
  ([23639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part017 : ℚ :=
  (1468727533 : ℚ) / 378840414359485440

def SurrogateDiagonalTailChunk001Sub000Block173Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23639
    = surrogateDiagTailX0RatChunk001Sub000Block173Part017

theorem surrogateDiagonalTailChunk001Sub000Block173Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part017] using hcert

def TailChunk001Sub000Block173Part018SupportExplicit : Finset ℕ :=
  ([23641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part018 : ℚ :=
  (155853314425 : ℚ) / 711005653813561707648

def SurrogateDiagonalTailChunk001Sub000Block173Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23641
    = surrogateDiagTailX0RatChunk001Sub000Block173Part018

theorem surrogateDiagonalTailChunk001Sub000Block173Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part018] using hcert

def TailChunk001Sub000Block173Part019SupportExplicit : Finset ℕ :=
  ([23642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block173Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23642
    = surrogateDiagTailX0RatChunk001Sub000Block173Part019

theorem surrogateDiagonalTailChunk001Sub000Block173Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part019] using hcert

def TailChunk001Sub000Block173Part020SupportExplicit : Finset ℕ :=
  ([23645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part020 : ℚ :=
  (1398374596375 : ℚ) / 319872346107129888768

def SurrogateDiagonalTailChunk001Sub000Block173Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23645
    = surrogateDiagTailX0RatChunk001Sub000Block173Part020

theorem surrogateDiagonalTailChunk001Sub000Block173Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part020] using hcert

def TailChunk001Sub000Block173Part021SupportExplicit : Finset ℕ :=
  ([23646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part021 : ℚ :=
  (20514647725 : ℚ) / 63857525646379008

def SurrogateDiagonalTailChunk001Sub000Block173Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23646
    = surrogateDiagTailX0RatChunk001Sub000Block173Part021

theorem surrogateDiagonalTailChunk001Sub000Block173Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part021] using hcert

def TailChunk001Sub000Block173Part022SupportExplicit : Finset ℕ :=
  ([23647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part022 : ℚ :=
  (258107645725 : ℚ) / 107249491914786865152

def SurrogateDiagonalTailChunk001Sub000Block173Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23647
    = surrogateDiagTailX0RatChunk001Sub000Block173Part022

theorem surrogateDiagonalTailChunk001Sub000Block173Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part022] using hcert

def TailChunk001Sub000Block173Part023SupportExplicit : Finset ℕ :=
  ([23649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part023 : ℚ :=
  (277392517175 : ℚ) / 11029721025543847872

def SurrogateDiagonalTailChunk001Sub000Block173Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23649
    = surrogateDiagTailX0RatChunk001Sub000Block173Part023

theorem surrogateDiagonalTailChunk001Sub000Block173Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part023] using hcert

def TailChunk001Sub000Block173Part024SupportExplicit : Finset ℕ :=
  ([23651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block173Part024 : ℚ :=
  (32214828475 : ℚ) / 182101391178435919872

def SurrogateDiagonalTailChunk001Sub000Block173Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23651
    = surrogateDiagTailX0RatChunk001Sub000Block173Part024

theorem surrogateDiagonalTailChunk001Sub000Block173Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block173Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block173Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block173Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block173Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block173Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block173HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block173Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block173Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block173Part000
    + surrogateDiagTailX0RatChunk001Sub000Block173Part001
    + surrogateDiagTailX0RatChunk001Sub000Block173Part002
    + surrogateDiagTailX0RatChunk001Sub000Block173Part003
    + surrogateDiagTailX0RatChunk001Sub000Block173Part004
    + surrogateDiagTailX0RatChunk001Sub000Block173Part005
    + surrogateDiagTailX0RatChunk001Sub000Block173Part006
    + surrogateDiagTailX0RatChunk001Sub000Block173Part007
    + surrogateDiagTailX0RatChunk001Sub000Block173Part008
    + surrogateDiagTailX0RatChunk001Sub000Block173Part009

def surrogateDiagonalTailChunk001Sub000Block173MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block173Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block173Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block173Part010
    + surrogateDiagTailX0RatChunk001Sub000Block173Part011
    + surrogateDiagTailX0RatChunk001Sub000Block173Part012
    + surrogateDiagTailX0RatChunk001Sub000Block173Part013
    + surrogateDiagTailX0RatChunk001Sub000Block173Part014
    + surrogateDiagTailX0RatChunk001Sub000Block173Part015
    + surrogateDiagTailX0RatChunk001Sub000Block173Part016
    + surrogateDiagTailX0RatChunk001Sub000Block173Part017
    + surrogateDiagTailX0RatChunk001Sub000Block173Part018
    + surrogateDiagTailX0RatChunk001Sub000Block173Part019

def surrogateDiagonalTailChunk001Sub000Block173TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block173Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block173Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block173Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block173Part020
    + surrogateDiagTailX0RatChunk001Sub000Block173Part021
    + surrogateDiagTailX0RatChunk001Sub000Block173Part022
    + surrogateDiagTailX0RatChunk001Sub000Block173Part023
    + surrogateDiagTailX0RatChunk001Sub000Block173Part024

def surrogateDiagonalTailChunk001Sub000Block173Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block173HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block173MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block173TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block173 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block173Part000
    + surrogateDiagTailX0RatChunk001Sub000Block173Part001
    + surrogateDiagTailX0RatChunk001Sub000Block173Part002
    + surrogateDiagTailX0RatChunk001Sub000Block173Part003
    + surrogateDiagTailX0RatChunk001Sub000Block173Part004
    + surrogateDiagTailX0RatChunk001Sub000Block173Part005
    + surrogateDiagTailX0RatChunk001Sub000Block173Part006
    + surrogateDiagTailX0RatChunk001Sub000Block173Part007
    + surrogateDiagTailX0RatChunk001Sub000Block173Part008
    + surrogateDiagTailX0RatChunk001Sub000Block173Part009
    + surrogateDiagTailX0RatChunk001Sub000Block173Part010
    + surrogateDiagTailX0RatChunk001Sub000Block173Part011
    + surrogateDiagTailX0RatChunk001Sub000Block173Part012
    + surrogateDiagTailX0RatChunk001Sub000Block173Part013
    + surrogateDiagTailX0RatChunk001Sub000Block173Part014
    + surrogateDiagTailX0RatChunk001Sub000Block173Part015
    + surrogateDiagTailX0RatChunk001Sub000Block173Part016
    + surrogateDiagTailX0RatChunk001Sub000Block173Part017
    + surrogateDiagTailX0RatChunk001Sub000Block173Part018
    + surrogateDiagTailX0RatChunk001Sub000Block173Part019
    + surrogateDiagTailX0RatChunk001Sub000Block173Part020
    + surrogateDiagTailX0RatChunk001Sub000Block173Part021
    + surrogateDiagTailX0RatChunk001Sub000Block173Part022
    + surrogateDiagTailX0RatChunk001Sub000Block173Part023
    + surrogateDiagTailX0RatChunk001Sub000Block173Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block173_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block173Head + surrogateDiagTailX0RatChunk001Sub000Block173Mid + surrogateDiagTailX0RatChunk001Sub000Block173Tail =
      surrogateDiagTailX0RatChunk001Sub000Block173 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block173Head surrogateDiagTailX0RatChunk001Sub000Block173Mid surrogateDiagTailX0RatChunk001Sub000Block173Tail surrogateDiagTailX0RatChunk001Sub000Block173
  ring

def SurrogateDiagonalTailChunk001Sub000Block173HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block173HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block173Head

def SurrogateDiagonalTailChunk001Sub000Block173MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block173MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block173Mid

def SurrogateDiagonalTailChunk001Sub000Block173TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block173TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block173Tail

theorem surrogateDiagonalTailChunk001Sub000Block173_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block173HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block173MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block173TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block173Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block173 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block173HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block173MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block173TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block173Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block173_eq_head_add_mid_add_tail

/-- Block 174 covers tail-support indices [14350,14375) and q from 23653 to 23691. -/

def TailChunk001Sub000Block174Part000SupportExplicit : Finset ℕ :=
  ([23653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part000 : ℚ :=
  (62127991801 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub000Block174Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23653
    = surrogateDiagTailX0RatChunk001Sub000Block174Part000

theorem surrogateDiagonalTailChunk001Sub000Block174Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part000] using hcert

def TailChunk001Sub000Block174Part001SupportExplicit : Finset ℕ :=
  ([23654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23654
    = surrogateDiagTailX0RatChunk001Sub000Block174Part001

theorem surrogateDiagonalTailChunk001Sub000Block174Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part001] using hcert

def TailChunk001Sub000Block174Part002SupportExplicit : Finset ℕ :=
  ([23655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part002 : ℚ :=
  (3096012868075 : ℚ) / 48610740494884405248

def SurrogateDiagonalTailChunk001Sub000Block174Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23655
    = surrogateDiagTailX0RatChunk001Sub000Block174Part002

theorem surrogateDiagonalTailChunk001Sub000Block174Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part002] using hcert

def TailChunk001Sub000Block174Part003SupportExplicit : Finset ℕ :=
  ([23657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part003 : ℚ :=
  (7953239209 : ℚ) / 28184916285141811200

def SurrogateDiagonalTailChunk001Sub000Block174Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23657
    = surrogateDiagTailX0RatChunk001Sub000Block174Part003

theorem surrogateDiagonalTailChunk001Sub000Block174Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part003] using hcert

def TailChunk001Sub000Block174Part004SupportExplicit : Finset ℕ :=
  ([23658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part004 : ℚ :=
  (971328373325 : ℚ) / 4830402557824017984

def SurrogateDiagonalTailChunk001Sub000Block174Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23658
    = surrogateDiagTailX0RatChunk001Sub000Block174Part004

theorem surrogateDiagonalTailChunk001Sub000Block174Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part004] using hcert

def TailChunk001Sub000Block174Part005SupportExplicit : Finset ℕ :=
  ([23659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part005 : ℚ :=
  (203952833 : ℚ) / 999173234688000000

def SurrogateDiagonalTailChunk001Sub000Block174Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23659
    = surrogateDiagTailX0RatChunk001Sub000Block174Part005

theorem surrogateDiagonalTailChunk001Sub000Block174Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part005] using hcert

def TailChunk001Sub000Block174Part006SupportExplicit : Finset ℕ :=
  ([23662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23662
    = surrogateDiagTailX0RatChunk001Sub000Block174Part006

theorem surrogateDiagonalTailChunk001Sub000Block174Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part006] using hcert

def TailChunk001Sub000Block174Part007SupportExplicit : Finset ℕ :=
  ([23663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23663
    = surrogateDiagTailX0RatChunk001Sub000Block174Part007

theorem surrogateDiagonalTailChunk001Sub000Block174Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part007] using hcert

def TailChunk001Sub000Block174Part008SupportExplicit : Finset ℕ :=
  ([23665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part008 : ℚ :=
  (466913198625 : ℚ) / 106985399638055550976

def SurrogateDiagonalTailChunk001Sub000Block174Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23665
    = surrogateDiagTailX0RatChunk001Sub000Block174Part008

theorem surrogateDiagonalTailChunk001Sub000Block174Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part008] using hcert

def TailChunk001Sub000Block174Part009SupportExplicit : Finset ℕ :=
  ([23666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23666
    = surrogateDiagTailX0RatChunk001Sub000Block174Part009

theorem surrogateDiagonalTailChunk001Sub000Block174Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part009] using hcert

def TailChunk001Sub000Block174Part010SupportExplicit : Finset ℕ :=
  ([23669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23669
    = surrogateDiagTailX0RatChunk001Sub000Block174Part010

theorem surrogateDiagonalTailChunk001Sub000Block174Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part010] using hcert

def TailChunk001Sub000Block174Part011SupportExplicit : Finset ℕ :=
  ([23671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23671
    = surrogateDiagTailX0RatChunk001Sub000Block174Part011

theorem surrogateDiagonalTailChunk001Sub000Block174Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part011] using hcert

def TailChunk001Sub000Block174Part012SupportExplicit : Finset ℕ :=
  ([23673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part012 : ℚ :=
  (1841483225 : ℚ) / 517974728263446528

def SurrogateDiagonalTailChunk001Sub000Block174Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23673
    = surrogateDiagTailX0RatChunk001Sub000Block174Part012

theorem surrogateDiagonalTailChunk001Sub000Block174Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part012] using hcert

def TailChunk001Sub000Block174Part013SupportExplicit : Finset ℕ :=
  ([23674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part013 : ℚ :=
  (221726844425 : ℚ) / 6800350770221285376

def SurrogateDiagonalTailChunk001Sub000Block174Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23674
    = surrogateDiagTailX0RatChunk001Sub000Block174Part013

theorem surrogateDiagonalTailChunk001Sub000Block174Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part013] using hcert

def TailChunk001Sub000Block174Part014SupportExplicit : Finset ℕ :=
  ([23677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23677
    = surrogateDiagTailX0RatChunk001Sub000Block174Part014

theorem surrogateDiagonalTailChunk001Sub000Block174Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part014] using hcert

def TailChunk001Sub000Block174Part015SupportExplicit : Finset ℕ :=
  ([23678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23678
    = surrogateDiagTailX0RatChunk001Sub000Block174Part015

theorem surrogateDiagonalTailChunk001Sub000Block174Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part015] using hcert

def TailChunk001Sub000Block174Part016SupportExplicit : Finset ℕ :=
  ([23681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part016 : ℚ :=
  (420880824625 : ℚ) / 81604209242655424512

def SurrogateDiagonalTailChunk001Sub000Block174Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23681
    = surrogateDiagTailX0RatChunk001Sub000Block174Part016

theorem surrogateDiagonalTailChunk001Sub000Block174Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part016] using hcert

def TailChunk001Sub000Block174Part017SupportExplicit : Finset ℕ :=
  ([23682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part017 : ℚ :=
  (486903669425 : ℚ) / 4850038315281436224

def SurrogateDiagonalTailChunk001Sub000Block174Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23682
    = surrogateDiagTailX0RatChunk001Sub000Block174Part017

theorem surrogateDiagonalTailChunk001Sub000Block174Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part017] using hcert

def TailChunk001Sub000Block174Part018SupportExplicit : Finset ℕ :=
  ([23683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part018 : ℚ :=
  (5818999519 : ℚ) / 5362853420916940800

def SurrogateDiagonalTailChunk001Sub000Block174Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23683
    = surrogateDiagTailX0RatChunk001Sub000Block174Part018

theorem surrogateDiagonalTailChunk001Sub000Block174Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part018] using hcert

def TailChunk001Sub000Block174Part019SupportExplicit : Finset ℕ :=
  ([23685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part019 : ℚ :=
  (117058563125 : ℚ) / 7938250791323406336

def SurrogateDiagonalTailChunk001Sub000Block174Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23685
    = surrogateDiagTailX0RatChunk001Sub000Block174Part019

theorem surrogateDiagonalTailChunk001Sub000Block174Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part019] using hcert

def TailChunk001Sub000Block174Part020SupportExplicit : Finset ℕ :=
  ([23686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part020 : ℚ :=
  (502367155 : ℚ) / 56890191414970368

def SurrogateDiagonalTailChunk001Sub000Block174Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23686
    = surrogateDiagTailX0RatChunk001Sub000Block174Part020

theorem surrogateDiagonalTailChunk001Sub000Block174Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part020] using hcert

def TailChunk001Sub000Block174Part021SupportExplicit : Finset ℕ :=
  ([23687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23687
    = surrogateDiagTailX0RatChunk001Sub000Block174Part021

theorem surrogateDiagonalTailChunk001Sub000Block174Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part021] using hcert

def TailChunk001Sub000Block174Part022SupportExplicit : Finset ℕ :=
  ([23689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block174Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23689
    = surrogateDiagTailX0RatChunk001Sub000Block174Part022

theorem surrogateDiagonalTailChunk001Sub000Block174Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part022] using hcert

def TailChunk001Sub000Block174Part023SupportExplicit : Finset ℕ :=
  ([23690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part023 : ℚ :=
  (784386970225 : ℚ) / 16231484244388773888

def SurrogateDiagonalTailChunk001Sub000Block174Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23690
    = surrogateDiagTailX0RatChunk001Sub000Block174Part023

theorem surrogateDiagonalTailChunk001Sub000Block174Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part023] using hcert

def TailChunk001Sub000Block174Part024SupportExplicit : Finset ℕ :=
  ([23691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block174Part024 : ℚ :=
  (5193158625 : ℚ) / 5847844771535716352

def SurrogateDiagonalTailChunk001Sub000Block174Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23691
    = surrogateDiagTailX0RatChunk001Sub000Block174Part024

theorem surrogateDiagonalTailChunk001Sub000Block174Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block174Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block174Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block174Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block174Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block174Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block174HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block174Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block174Part000
    + surrogateDiagTailX0RatChunk001Sub000Block174Part001
    + surrogateDiagTailX0RatChunk001Sub000Block174Part002
    + surrogateDiagTailX0RatChunk001Sub000Block174Part003
    + surrogateDiagTailX0RatChunk001Sub000Block174Part004
    + surrogateDiagTailX0RatChunk001Sub000Block174Part005
    + surrogateDiagTailX0RatChunk001Sub000Block174Part006
    + surrogateDiagTailX0RatChunk001Sub000Block174Part007
    + surrogateDiagTailX0RatChunk001Sub000Block174Part008
    + surrogateDiagTailX0RatChunk001Sub000Block174Part009

def surrogateDiagonalTailChunk001Sub000Block174MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block174Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block174Part010
    + surrogateDiagTailX0RatChunk001Sub000Block174Part011
    + surrogateDiagTailX0RatChunk001Sub000Block174Part012
    + surrogateDiagTailX0RatChunk001Sub000Block174Part013
    + surrogateDiagTailX0RatChunk001Sub000Block174Part014
    + surrogateDiagTailX0RatChunk001Sub000Block174Part015
    + surrogateDiagTailX0RatChunk001Sub000Block174Part016
    + surrogateDiagTailX0RatChunk001Sub000Block174Part017
    + surrogateDiagTailX0RatChunk001Sub000Block174Part018
    + surrogateDiagTailX0RatChunk001Sub000Block174Part019

def surrogateDiagonalTailChunk001Sub000Block174TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block174Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block174Part020
    + surrogateDiagTailX0RatChunk001Sub000Block174Part021
    + surrogateDiagTailX0RatChunk001Sub000Block174Part022
    + surrogateDiagTailX0RatChunk001Sub000Block174Part023
    + surrogateDiagTailX0RatChunk001Sub000Block174Part024

def surrogateDiagonalTailChunk001Sub000Block174Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block174HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block174MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block174TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block174 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block174Part000
    + surrogateDiagTailX0RatChunk001Sub000Block174Part001
    + surrogateDiagTailX0RatChunk001Sub000Block174Part002
    + surrogateDiagTailX0RatChunk001Sub000Block174Part003
    + surrogateDiagTailX0RatChunk001Sub000Block174Part004
    + surrogateDiagTailX0RatChunk001Sub000Block174Part005
    + surrogateDiagTailX0RatChunk001Sub000Block174Part006
    + surrogateDiagTailX0RatChunk001Sub000Block174Part007
    + surrogateDiagTailX0RatChunk001Sub000Block174Part008
    + surrogateDiagTailX0RatChunk001Sub000Block174Part009
    + surrogateDiagTailX0RatChunk001Sub000Block174Part010
    + surrogateDiagTailX0RatChunk001Sub000Block174Part011
    + surrogateDiagTailX0RatChunk001Sub000Block174Part012
    + surrogateDiagTailX0RatChunk001Sub000Block174Part013
    + surrogateDiagTailX0RatChunk001Sub000Block174Part014
    + surrogateDiagTailX0RatChunk001Sub000Block174Part015
    + surrogateDiagTailX0RatChunk001Sub000Block174Part016
    + surrogateDiagTailX0RatChunk001Sub000Block174Part017
    + surrogateDiagTailX0RatChunk001Sub000Block174Part018
    + surrogateDiagTailX0RatChunk001Sub000Block174Part019
    + surrogateDiagTailX0RatChunk001Sub000Block174Part020
    + surrogateDiagTailX0RatChunk001Sub000Block174Part021
    + surrogateDiagTailX0RatChunk001Sub000Block174Part022
    + surrogateDiagTailX0RatChunk001Sub000Block174Part023
    + surrogateDiagTailX0RatChunk001Sub000Block174Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block174_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block174Head + surrogateDiagTailX0RatChunk001Sub000Block174Mid + surrogateDiagTailX0RatChunk001Sub000Block174Tail =
      surrogateDiagTailX0RatChunk001Sub000Block174 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block174Head surrogateDiagTailX0RatChunk001Sub000Block174Mid surrogateDiagTailX0RatChunk001Sub000Block174Tail surrogateDiagTailX0RatChunk001Sub000Block174
  ring

def SurrogateDiagonalTailChunk001Sub000Block174HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block174HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block174Head

def SurrogateDiagonalTailChunk001Sub000Block174MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block174MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block174Mid

def SurrogateDiagonalTailChunk001Sub000Block174TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block174TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block174Tail

theorem surrogateDiagonalTailChunk001Sub000Block174_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block174HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block174MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block174TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block174Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block174 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block174HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block174MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block174TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block174Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block174_eq_head_add_mid_add_tail

/-- Block 175 covers tail-support indices [14375,14400) and q from 23693 to 23731. -/

def TailChunk001Sub000Block175Part000SupportExplicit : Finset ℕ :=
  ([23693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part000 : ℚ :=
  (190796769175 : ℚ) / 125512267307526070272

def SurrogateDiagonalTailChunk001Sub000Block175Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23693
    = surrogateDiagTailX0RatChunk001Sub000Block175Part000

theorem surrogateDiagonalTailChunk001Sub000Block175Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part000] using hcert

def TailChunk001Sub000Block175Part001SupportExplicit : Finset ℕ :=
  ([23694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part001 : ℚ :=
  (40304220001 : ℚ) / 262868737570867200

def SurrogateDiagonalTailChunk001Sub000Block175Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23694
    = surrogateDiagTailX0RatChunk001Sub000Block175Part001

theorem surrogateDiagonalTailChunk001Sub000Block175Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part001] using hcert

def TailChunk001Sub000Block175Part002SupportExplicit : Finset ℕ :=
  ([23695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part002 : ℚ :=
  (515932980475 : ℚ) / 43311040586501455872

def SurrogateDiagonalTailChunk001Sub000Block175Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23695
    = surrogateDiagTailX0RatChunk001Sub000Block175Part002

theorem surrogateDiagonalTailChunk001Sub000Block175Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part002] using hcert

def TailChunk001Sub000Block175Part003SupportExplicit : Finset ℕ :=
  ([23699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part003 : ℚ :=
  (156486219925 : ℚ) / 142851676726154506752

def SurrogateDiagonalTailChunk001Sub000Block175Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23699
    = surrogateDiagTailX0RatChunk001Sub000Block175Part003

theorem surrogateDiagonalTailChunk001Sub000Block175Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part003] using hcert

def TailChunk001Sub000Block175Part004SupportExplicit : Finset ℕ :=
  ([23701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part004 : ℚ :=
  (32132520825 : ℚ) / 249560027764415266816

def SurrogateDiagonalTailChunk001Sub000Block175Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23701
    = surrogateDiagTailX0RatChunk001Sub000Block175Part004

theorem surrogateDiagonalTailChunk001Sub000Block175Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part004] using hcert

def TailChunk001Sub000Block175Part005SupportExplicit : Finset ℕ :=
  ([23702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part005 : ℚ :=
  (9971239075 : ℚ) / 491857768833149952

def SurrogateDiagonalTailChunk001Sub000Block175Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23702
    = surrogateDiagTailX0RatChunk001Sub000Block175Part005

theorem surrogateDiagonalTailChunk001Sub000Block175Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part005] using hcert

def TailChunk001Sub000Block175Part006SupportExplicit : Finset ℕ :=
  ([23703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part006 : ℚ :=
  (5001 : ℚ) / 1246402592000000

def SurrogateDiagonalTailChunk001Sub000Block175Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23703
    = surrogateDiagTailX0RatChunk001Sub000Block175Part006

theorem surrogateDiagonalTailChunk001Sub000Block175Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part006] using hcert

def TailChunk001Sub000Block175Part007SupportExplicit : Finset ℕ :=
  ([23705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part007 : ℚ :=
  (6521891221 : ℚ) / 875388098611200000

def SurrogateDiagonalTailChunk001Sub000Block175Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23705
    = surrogateDiagTailX0RatChunk001Sub000Block175Part007

theorem surrogateDiagonalTailChunk001Sub000Block175Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part007] using hcert

def TailChunk001Sub000Block175Part008SupportExplicit : Finset ℕ :=
  ([23707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part008 : ℚ :=
  (950925769 : ℚ) / 7497047949768000000

def SurrogateDiagonalTailChunk001Sub000Block175Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23707
    = surrogateDiagTailX0RatChunk001Sub000Block175Part008

theorem surrogateDiagonalTailChunk001Sub000Block175Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part008] using hcert

def TailChunk001Sub000Block175Part009SupportExplicit : Finset ℕ :=
  ([23709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part009 : ℚ :=
  (878671956925 : ℚ) / 83943725880857591808

def SurrogateDiagonalTailChunk001Sub000Block175Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23709
    = surrogateDiagTailX0RatChunk001Sub000Block175Part009

theorem surrogateDiagonalTailChunk001Sub000Block175Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part009] using hcert

def TailChunk001Sub000Block175Part010SupportExplicit : Finset ℕ :=
  ([23710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part010 : ℚ :=
  (9376299883 : ℚ) / 269276804463974400

def SurrogateDiagonalTailChunk001Sub000Block175Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23710
    = surrogateDiagTailX0RatChunk001Sub000Block175Part010

theorem surrogateDiagonalTailChunk001Sub000Block175Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part010] using hcert

def TailChunk001Sub000Block175Part011SupportExplicit : Finset ℕ :=
  ([23711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part011 : ℚ :=
  (59598287 : ℚ) / 461356796908800000

def SurrogateDiagonalTailChunk001Sub000Block175Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23711
    = surrogateDiagTailX0RatChunk001Sub000Block175Part011

theorem surrogateDiagonalTailChunk001Sub000Block175Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part011] using hcert

def TailChunk001Sub000Block175Part012SupportExplicit : Finset ℕ :=
  ([23713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part012 : ℚ :=
  (4508413047 : ℚ) / 8790330774457302400

def SurrogateDiagonalTailChunk001Sub000Block175Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23713
    = surrogateDiagTailX0RatChunk001Sub000Block175Part012

theorem surrogateDiagonalTailChunk001Sub000Block175Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part012] using hcert

def TailChunk001Sub000Block175Part013SupportExplicit : Finset ℕ :=
  ([23714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part013 : ℚ :=
  (952186947 : ℚ) / 607841163769302400

def SurrogateDiagonalTailChunk001Sub000Block175Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23714
    = surrogateDiagTailX0RatChunk001Sub000Block175Part013

theorem surrogateDiagonalTailChunk001Sub000Block175Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part013] using hcert

def TailChunk001Sub000Block175Part014SupportExplicit : Finset ℕ :=
  ([23717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part014 : ℚ :=
  (7609031329 : ℚ) / 28184916285141811200

def SurrogateDiagonalTailChunk001Sub000Block175Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23717
    = surrogateDiagTailX0RatChunk001Sub000Block175Part014

theorem surrogateDiagonalTailChunk001Sub000Block175Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part014] using hcert

def TailChunk001Sub000Block175Part015SupportExplicit : Finset ℕ :=
  ([23718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part015 : ℚ :=
  (9194106425 : ℚ) / 79544618351801856

def SurrogateDiagonalTailChunk001Sub000Block175Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23718
    = surrogateDiagTailX0RatChunk001Sub000Block175Part015

theorem surrogateDiagonalTailChunk001Sub000Block175Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part015] using hcert

def TailChunk001Sub000Block175Part016SupportExplicit : Finset ℕ :=
  ([23719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block175Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23719
    = surrogateDiagTailX0RatChunk001Sub000Block175Part016

theorem surrogateDiagonalTailChunk001Sub000Block175Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part016] using hcert

def TailChunk001Sub000Block175Part017SupportExplicit : Finset ℕ :=
  ([23721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part017 : ℚ :=
  (125025 : ℚ) / 31254836187095168

def SurrogateDiagonalTailChunk001Sub000Block175Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23721
    = surrogateDiagTailX0RatChunk001Sub000Block175Part017

theorem surrogateDiagonalTailChunk001Sub000Block175Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part017] using hcert

def TailChunk001Sub000Block175Part018SupportExplicit : Finset ℕ :=
  ([23722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part018 : ℚ :=
  (33326066275 : ℚ) / 10647303782740918272

def SurrogateDiagonalTailChunk001Sub000Block175Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23722
    = surrogateDiagTailX0RatChunk001Sub000Block175Part018

theorem surrogateDiagonalTailChunk001Sub000Block175Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part018] using hcert

def TailChunk001Sub000Block175Part019SupportExplicit : Finset ℕ :=
  ([23723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part019 : ℚ :=
  (718202946575 : ℚ) / 213488984482140939264

def SurrogateDiagonalTailChunk001Sub000Block175Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23723
    = surrogateDiagTailX0RatChunk001Sub000Block175Part019

theorem surrogateDiagonalTailChunk001Sub000Block175Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part019] using hcert

def TailChunk001Sub000Block175Part020SupportExplicit : Finset ℕ :=
  ([23726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block175Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23726
    = surrogateDiagTailX0RatChunk001Sub000Block175Part020

theorem surrogateDiagonalTailChunk001Sub000Block175Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part020] using hcert

def TailChunk001Sub000Block175Part021SupportExplicit : Finset ℕ :=
  ([23727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part021 : ℚ :=
  (6958173993 : ℚ) / 1417696787066214400

def SurrogateDiagonalTailChunk001Sub000Block175Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23727
    = surrogateDiagTailX0RatChunk001Sub000Block175Part021

theorem surrogateDiagonalTailChunk001Sub000Block175Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part021] using hcert

def TailChunk001Sub000Block175Part022SupportExplicit : Finset ℕ :=
  ([23729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part022 : ℚ :=
  (1877093969 : ℚ) / 9792588370400870400

def SurrogateDiagonalTailChunk001Sub000Block175Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23729
    = surrogateDiagTailX0RatChunk001Sub000Block175Part022

theorem surrogateDiagonalTailChunk001Sub000Block175Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part022] using hcert

def TailChunk001Sub000Block175Part023SupportExplicit : Finset ℕ :=
  ([23730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part023 : ℚ :=
  (259521778975 : ℚ) / 522160370375196672

def SurrogateDiagonalTailChunk001Sub000Block175Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23730
    = surrogateDiagTailX0RatChunk001Sub000Block175Part023

theorem surrogateDiagonalTailChunk001Sub000Block175Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part023] using hcert

def TailChunk001Sub000Block175Part024SupportExplicit : Finset ℕ :=
  ([23731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block175Part024 : ℚ :=
  (43862791525 : ℚ) / 70751020958783373312

def SurrogateDiagonalTailChunk001Sub000Block175Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23731
    = surrogateDiagTailX0RatChunk001Sub000Block175Part024

theorem surrogateDiagonalTailChunk001Sub000Block175Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block175Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block175Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block175Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block175Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block175Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block175HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block175Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block175Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block175Part000
    + surrogateDiagTailX0RatChunk001Sub000Block175Part001
    + surrogateDiagTailX0RatChunk001Sub000Block175Part002
    + surrogateDiagTailX0RatChunk001Sub000Block175Part003
    + surrogateDiagTailX0RatChunk001Sub000Block175Part004
    + surrogateDiagTailX0RatChunk001Sub000Block175Part005
    + surrogateDiagTailX0RatChunk001Sub000Block175Part006
    + surrogateDiagTailX0RatChunk001Sub000Block175Part007
    + surrogateDiagTailX0RatChunk001Sub000Block175Part008
    + surrogateDiagTailX0RatChunk001Sub000Block175Part009

def surrogateDiagonalTailChunk001Sub000Block175MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block175Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block175Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block175Part010
    + surrogateDiagTailX0RatChunk001Sub000Block175Part011
    + surrogateDiagTailX0RatChunk001Sub000Block175Part012
    + surrogateDiagTailX0RatChunk001Sub000Block175Part013
    + surrogateDiagTailX0RatChunk001Sub000Block175Part014
    + surrogateDiagTailX0RatChunk001Sub000Block175Part015
    + surrogateDiagTailX0RatChunk001Sub000Block175Part016
    + surrogateDiagTailX0RatChunk001Sub000Block175Part017
    + surrogateDiagTailX0RatChunk001Sub000Block175Part018
    + surrogateDiagTailX0RatChunk001Sub000Block175Part019

def surrogateDiagonalTailChunk001Sub000Block175TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block175Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block175Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block175Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block175Part020
    + surrogateDiagTailX0RatChunk001Sub000Block175Part021
    + surrogateDiagTailX0RatChunk001Sub000Block175Part022
    + surrogateDiagTailX0RatChunk001Sub000Block175Part023
    + surrogateDiagTailX0RatChunk001Sub000Block175Part024

def surrogateDiagonalTailChunk001Sub000Block175Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block175HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block175MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block175TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block175 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block175Part000
    + surrogateDiagTailX0RatChunk001Sub000Block175Part001
    + surrogateDiagTailX0RatChunk001Sub000Block175Part002
    + surrogateDiagTailX0RatChunk001Sub000Block175Part003
    + surrogateDiagTailX0RatChunk001Sub000Block175Part004
    + surrogateDiagTailX0RatChunk001Sub000Block175Part005
    + surrogateDiagTailX0RatChunk001Sub000Block175Part006
    + surrogateDiagTailX0RatChunk001Sub000Block175Part007
    + surrogateDiagTailX0RatChunk001Sub000Block175Part008
    + surrogateDiagTailX0RatChunk001Sub000Block175Part009
    + surrogateDiagTailX0RatChunk001Sub000Block175Part010
    + surrogateDiagTailX0RatChunk001Sub000Block175Part011
    + surrogateDiagTailX0RatChunk001Sub000Block175Part012
    + surrogateDiagTailX0RatChunk001Sub000Block175Part013
    + surrogateDiagTailX0RatChunk001Sub000Block175Part014
    + surrogateDiagTailX0RatChunk001Sub000Block175Part015
    + surrogateDiagTailX0RatChunk001Sub000Block175Part016
    + surrogateDiagTailX0RatChunk001Sub000Block175Part017
    + surrogateDiagTailX0RatChunk001Sub000Block175Part018
    + surrogateDiagTailX0RatChunk001Sub000Block175Part019
    + surrogateDiagTailX0RatChunk001Sub000Block175Part020
    + surrogateDiagTailX0RatChunk001Sub000Block175Part021
    + surrogateDiagTailX0RatChunk001Sub000Block175Part022
    + surrogateDiagTailX0RatChunk001Sub000Block175Part023
    + surrogateDiagTailX0RatChunk001Sub000Block175Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block175_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block175Head + surrogateDiagTailX0RatChunk001Sub000Block175Mid + surrogateDiagTailX0RatChunk001Sub000Block175Tail =
      surrogateDiagTailX0RatChunk001Sub000Block175 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block175Head surrogateDiagTailX0RatChunk001Sub000Block175Mid surrogateDiagTailX0RatChunk001Sub000Block175Tail surrogateDiagTailX0RatChunk001Sub000Block175
  ring

def SurrogateDiagonalTailChunk001Sub000Block175HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block175HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block175Head

def SurrogateDiagonalTailChunk001Sub000Block175MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block175MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block175Mid

def SurrogateDiagonalTailChunk001Sub000Block175TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block175TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block175Tail

theorem surrogateDiagonalTailChunk001Sub000Block175_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block175HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block175MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block175TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block175Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block175 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block175HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block175MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block175TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block175Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block175_eq_head_add_mid_add_tail

/-- Block 176 covers tail-support indices [14400,14425) and q from 23734 to 23777. -/

def TailChunk001Sub000Block176Part000SupportExplicit : Finset ℕ :=
  ([23734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23734
    = surrogateDiagTailX0RatChunk001Sub000Block176Part000

theorem surrogateDiagonalTailChunk001Sub000Block176Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part000] using hcert

def TailChunk001Sub000Block176Part001SupportExplicit : Finset ℕ :=
  ([23735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part001 : ℚ :=
  (1202925857 : ℚ) / 229291596349440000

def SurrogateDiagonalTailChunk001Sub000Block176Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23735
    = surrogateDiagTailX0RatChunk001Sub000Block176Part001

theorem surrogateDiagonalTailChunk001Sub000Block176Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part001] using hcert

def TailChunk001Sub000Block176Part002SupportExplicit : Finset ℕ :=
  ([23737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part002 : ℚ :=
  (28805246773 : ℚ) / 17119482980289667200

def SurrogateDiagonalTailChunk001Sub000Block176Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23737
    = surrogateDiagTailX0RatChunk001Sub000Block176Part002

theorem surrogateDiagonalTailChunk001Sub000Block176Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part002] using hcert

def TailChunk001Sub000Block176Part003SupportExplicit : Finset ℕ :=
  ([23738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part003 : ℚ :=
  (8166173177 : ℚ) / 312569061824102400

def SurrogateDiagonalTailChunk001Sub000Block176Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23738
    = surrogateDiagTailX0RatChunk001Sub000Block176Part003

theorem surrogateDiagonalTailChunk001Sub000Block176Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part003] using hcert

def TailChunk001Sub000Block176Part004SupportExplicit : Finset ℕ :=
  ([23739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part004 : ℚ :=
  (1959305563 : ℚ) / 1855796957046374400

def SurrogateDiagonalTailChunk001Sub000Block176Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23739
    = surrogateDiagTailX0RatChunk001Sub000Block176Part004

theorem surrogateDiagonalTailChunk001Sub000Block176Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part004] using hcert

def TailChunk001Sub000Block176Part005SupportExplicit : Finset ℕ :=
  ([23741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23741
    = surrogateDiagTailX0RatChunk001Sub000Block176Part005

theorem surrogateDiagonalTailChunk001Sub000Block176Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part005] using hcert

def TailChunk001Sub000Block176Part006SupportExplicit : Finset ℕ :=
  ([23743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23743
    = surrogateDiagTailX0RatChunk001Sub000Block176Part006

theorem surrogateDiagonalTailChunk001Sub000Block176Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part006] using hcert

def TailChunk001Sub000Block176Part007SupportExplicit : Finset ℕ :=
  ([23745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part007 : ℚ :=
  (365876401725 : ℚ) / 21384124230519586816

def SurrogateDiagonalTailChunk001Sub000Block176Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23745
    = surrogateDiagTailX0RatChunk001Sub000Block176Part007

theorem surrogateDiagonalTailChunk001Sub000Block176Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part007] using hcert

def TailChunk001Sub000Block176Part008SupportExplicit : Finset ℕ :=
  ([23746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part008 : ℚ :=
  (5105525389 : ℚ) / 1725143875639171200

def SurrogateDiagonalTailChunk001Sub000Block176Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23746
    = surrogateDiagTailX0RatChunk001Sub000Block176Part008

theorem surrogateDiagonalTailChunk001Sub000Block176Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part008] using hcert

def TailChunk001Sub000Block176Part009SupportExplicit : Finset ℕ :=
  ([23747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23747
    = surrogateDiagTailX0RatChunk001Sub000Block176Part009

theorem surrogateDiagonalTailChunk001Sub000Block176Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part009] using hcert

def TailChunk001Sub000Block176Part010SupportExplicit : Finset ℕ :=
  ([23749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part010 : ℚ :=
  (39516669253 : ℚ) / 16521480468902707200

def SurrogateDiagonalTailChunk001Sub000Block176Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23749
    = surrogateDiagTailX0RatChunk001Sub000Block176Part010

theorem surrogateDiagonalTailChunk001Sub000Block176Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part010] using hcert

def TailChunk001Sub000Block176Part011SupportExplicit : Finset ℕ :=
  ([23753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23753
    = surrogateDiagTailX0RatChunk001Sub000Block176Part011

theorem surrogateDiagonalTailChunk001Sub000Block176Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part011] using hcert

def TailChunk001Sub000Block176Part012SupportExplicit : Finset ℕ :=
  ([23754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part012 : ℚ :=
  (998511924325 : ℚ) / 8483602387790757888

def SurrogateDiagonalTailChunk001Sub000Block176Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23754
    = surrogateDiagTailX0RatChunk001Sub000Block176Part012

theorem surrogateDiagonalTailChunk001Sub000Block176Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part012] using hcert

def TailChunk001Sub000Block176Part013SupportExplicit : Finset ℕ :=
  ([23755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part013 : ℚ :=
  (3763751583 : ℚ) / 868980428000000000

def SurrogateDiagonalTailChunk001Sub000Block176Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23755
    = surrogateDiagTailX0RatChunk001Sub000Block176Part013

theorem surrogateDiagonalTailChunk001Sub000Block176Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part013] using hcert

def TailChunk001Sub000Block176Part014SupportExplicit : Finset ℕ :=
  ([23757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part014 : ℚ :=
  (125025 : ℚ) / 31445027339489408

def SurrogateDiagonalTailChunk001Sub000Block176Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23757
    = surrogateDiagTailX0RatChunk001Sub000Block176Part014

theorem surrogateDiagonalTailChunk001Sub000Block176Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part014] using hcert

def TailChunk001Sub000Block176Part015SupportExplicit : Finset ℕ :=
  ([23758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part015 : ℚ :=
  (30054827425 : ℚ) / 1489576276594262016

def SurrogateDiagonalTailChunk001Sub000Block176Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23758
    = surrogateDiagTailX0RatChunk001Sub000Block176Part015

theorem surrogateDiagonalTailChunk001Sub000Block176Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part015] using hcert

def TailChunk001Sub000Block176Part016SupportExplicit : Finset ℕ :=
  ([23759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part016 : ℚ :=
  (45493539625 : ℚ) / 110735053791263244288

def SurrogateDiagonalTailChunk001Sub000Block176Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23759
    = surrogateDiagTailX0RatChunk001Sub000Block176Part016

theorem surrogateDiagonalTailChunk001Sub000Block176Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part016] using hcert

def TailChunk001Sub000Block176Part017SupportExplicit : Finset ℕ :=
  ([23761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23761
    = surrogateDiagTailX0RatChunk001Sub000Block176Part017

theorem surrogateDiagonalTailChunk001Sub000Block176Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part017] using hcert

def TailChunk001Sub000Block176Part018SupportExplicit : Finset ℕ :=
  ([23766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part018 : ℚ :=
  (506239257575 : ℚ) / 3797945392293740544

def SurrogateDiagonalTailChunk001Sub000Block176Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23766
    = surrogateDiagTailX0RatChunk001Sub000Block176Part018

theorem surrogateDiagonalTailChunk001Sub000Block176Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part018] using hcert

def TailChunk001Sub000Block176Part019SupportExplicit : Finset ℕ :=
  ([23767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23767
    = surrogateDiagTailX0RatChunk001Sub000Block176Part019

theorem surrogateDiagonalTailChunk001Sub000Block176Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part019] using hcert

def TailChunk001Sub000Block176Part020SupportExplicit : Finset ℕ :=
  ([23770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part020 : ℚ :=
  (235593759175 : ℚ) / 6800350770221285376

def SurrogateDiagonalTailChunk001Sub000Block176Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23770
    = surrogateDiagTailX0RatChunk001Sub000Block176Part020

theorem surrogateDiagonalTailChunk001Sub000Block176Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part020] using hcert

def TailChunk001Sub000Block176Part021SupportExplicit : Finset ℕ :=
  ([23771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part021 : ℚ :=
  (1954036957 : ℚ) / 1814348077056000000

def SurrogateDiagonalTailChunk001Sub000Block176Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23771
    = surrogateDiagTailX0RatChunk001Sub000Block176Part021

theorem surrogateDiagonalTailChunk001Sub000Block176Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part021] using hcert

def TailChunk001Sub000Block176Part022SupportExplicit : Finset ℕ :=
  ([23773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23773
    = surrogateDiagTailX0RatChunk001Sub000Block176Part022

theorem surrogateDiagonalTailChunk001Sub000Block176Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part022] using hcert

def TailChunk001Sub000Block176Part023SupportExplicit : Finset ℕ :=
  ([23774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block176Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23774
    = surrogateDiagTailX0RatChunk001Sub000Block176Part023

theorem surrogateDiagonalTailChunk001Sub000Block176Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part023] using hcert

def TailChunk001Sub000Block176Part024SupportExplicit : Finset ℕ :=
  ([23777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block176Part024 : ℚ :=
  (1824222401 : ℚ) / 950558460954255360

def SurrogateDiagonalTailChunk001Sub000Block176Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23777
    = surrogateDiagTailX0RatChunk001Sub000Block176Part024

theorem surrogateDiagonalTailChunk001Sub000Block176Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block176Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block176Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block176Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block176Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block176Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block176HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block176Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block176Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block176Part000
    + surrogateDiagTailX0RatChunk001Sub000Block176Part001
    + surrogateDiagTailX0RatChunk001Sub000Block176Part002
    + surrogateDiagTailX0RatChunk001Sub000Block176Part003
    + surrogateDiagTailX0RatChunk001Sub000Block176Part004
    + surrogateDiagTailX0RatChunk001Sub000Block176Part005
    + surrogateDiagTailX0RatChunk001Sub000Block176Part006
    + surrogateDiagTailX0RatChunk001Sub000Block176Part007
    + surrogateDiagTailX0RatChunk001Sub000Block176Part008
    + surrogateDiagTailX0RatChunk001Sub000Block176Part009

def surrogateDiagonalTailChunk001Sub000Block176MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block176Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block176Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block176Part010
    + surrogateDiagTailX0RatChunk001Sub000Block176Part011
    + surrogateDiagTailX0RatChunk001Sub000Block176Part012
    + surrogateDiagTailX0RatChunk001Sub000Block176Part013
    + surrogateDiagTailX0RatChunk001Sub000Block176Part014
    + surrogateDiagTailX0RatChunk001Sub000Block176Part015
    + surrogateDiagTailX0RatChunk001Sub000Block176Part016
    + surrogateDiagTailX0RatChunk001Sub000Block176Part017
    + surrogateDiagTailX0RatChunk001Sub000Block176Part018
    + surrogateDiagTailX0RatChunk001Sub000Block176Part019

def surrogateDiagonalTailChunk001Sub000Block176TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block176Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block176Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block176Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block176Part020
    + surrogateDiagTailX0RatChunk001Sub000Block176Part021
    + surrogateDiagTailX0RatChunk001Sub000Block176Part022
    + surrogateDiagTailX0RatChunk001Sub000Block176Part023
    + surrogateDiagTailX0RatChunk001Sub000Block176Part024

def surrogateDiagonalTailChunk001Sub000Block176Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block176HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block176MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block176TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block176 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block176Part000
    + surrogateDiagTailX0RatChunk001Sub000Block176Part001
    + surrogateDiagTailX0RatChunk001Sub000Block176Part002
    + surrogateDiagTailX0RatChunk001Sub000Block176Part003
    + surrogateDiagTailX0RatChunk001Sub000Block176Part004
    + surrogateDiagTailX0RatChunk001Sub000Block176Part005
    + surrogateDiagTailX0RatChunk001Sub000Block176Part006
    + surrogateDiagTailX0RatChunk001Sub000Block176Part007
    + surrogateDiagTailX0RatChunk001Sub000Block176Part008
    + surrogateDiagTailX0RatChunk001Sub000Block176Part009
    + surrogateDiagTailX0RatChunk001Sub000Block176Part010
    + surrogateDiagTailX0RatChunk001Sub000Block176Part011
    + surrogateDiagTailX0RatChunk001Sub000Block176Part012
    + surrogateDiagTailX0RatChunk001Sub000Block176Part013
    + surrogateDiagTailX0RatChunk001Sub000Block176Part014
    + surrogateDiagTailX0RatChunk001Sub000Block176Part015
    + surrogateDiagTailX0RatChunk001Sub000Block176Part016
    + surrogateDiagTailX0RatChunk001Sub000Block176Part017
    + surrogateDiagTailX0RatChunk001Sub000Block176Part018
    + surrogateDiagTailX0RatChunk001Sub000Block176Part019
    + surrogateDiagTailX0RatChunk001Sub000Block176Part020
    + surrogateDiagTailX0RatChunk001Sub000Block176Part021
    + surrogateDiagTailX0RatChunk001Sub000Block176Part022
    + surrogateDiagTailX0RatChunk001Sub000Block176Part023
    + surrogateDiagTailX0RatChunk001Sub000Block176Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block176_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block176Head + surrogateDiagTailX0RatChunk001Sub000Block176Mid + surrogateDiagTailX0RatChunk001Sub000Block176Tail =
      surrogateDiagTailX0RatChunk001Sub000Block176 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block176Head surrogateDiagTailX0RatChunk001Sub000Block176Mid surrogateDiagTailX0RatChunk001Sub000Block176Tail surrogateDiagTailX0RatChunk001Sub000Block176
  ring

def SurrogateDiagonalTailChunk001Sub000Block176HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block176HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block176Head

def SurrogateDiagonalTailChunk001Sub000Block176MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block176MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block176Mid

def SurrogateDiagonalTailChunk001Sub000Block176TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block176TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block176Tail

theorem surrogateDiagonalTailChunk001Sub000Block176_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block176HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block176MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block176TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block176Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block176 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block176HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block176MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block176TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block176Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block176_eq_head_add_mid_add_tail

/-- Block 177 covers tail-support indices [14425,14450) and q from 23779 to 23815. -/

def TailChunk001Sub000Block177Part000SupportExplicit : Finset ℕ :=
  ([23779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part000 : ℚ :=
  (445252050125 : ℚ) / 186628272936810292224

def SurrogateDiagonalTailChunk001Sub000Block177Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23779
    = surrogateDiagTailX0RatChunk001Sub000Block177Part000

theorem surrogateDiagonalTailChunk001Sub000Block177Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part000] using hcert

def TailChunk001Sub000Block177Part001SupportExplicit : Finset ℕ :=
  ([23781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part001 : ℚ :=
  (41675 : ℚ) / 10524100924849536

def SurrogateDiagonalTailChunk001Sub000Block177Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23781
    = surrogateDiagTailX0RatChunk001Sub000Block177Part001

theorem surrogateDiagonalTailChunk001Sub000Block177Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part001] using hcert

def TailChunk001Sub000Block177Part002SupportExplicit : Finset ℕ :=
  ([23782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part002 : ℚ :=
  (5202472837 : ℚ) / 262270176730636800

def SurrogateDiagonalTailChunk001Sub000Block177Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23782
    = surrogateDiagTailX0RatChunk001Sub000Block177Part002

theorem surrogateDiagonalTailChunk001Sub000Block177Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part002] using hcert

def TailChunk001Sub000Block177Part003SupportExplicit : Finset ℕ :=
  ([23783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part003 : ℚ :=
  (10313976925 : ℚ) / 17387333105049796608

def SurrogateDiagonalTailChunk001Sub000Block177Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23783
    = surrogateDiagTailX0RatChunk001Sub000Block177Part003

theorem surrogateDiagonalTailChunk001Sub000Block177Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part003] using hcert

def TailChunk001Sub000Block177Part004SupportExplicit : Finset ℕ :=
  ([23785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part004 : ℚ :=
  (30042086843 : ℚ) / 5832633958941081600

def SurrogateDiagonalTailChunk001Sub000Block177Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23785
    = surrogateDiagTailX0RatChunk001Sub000Block177Part004

theorem surrogateDiagonalTailChunk001Sub000Block177Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part004] using hcert

def TailChunk001Sub000Block177Part005SupportExplicit : Finset ℕ :=
  ([23786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part005 : ℚ :=
  (10041835825 : ℚ) / 498871672720627392

def SurrogateDiagonalTailChunk001Sub000Block177Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23786
    = surrogateDiagTailX0RatChunk001Sub000Block177Part005

theorem surrogateDiagonalTailChunk001Sub000Block177Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part005] using hcert

def TailChunk001Sub000Block177Part006SupportExplicit : Finset ℕ :=
  ([23789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block177Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23789
    = surrogateDiagTailX0RatChunk001Sub000Block177Part006

theorem surrogateDiagonalTailChunk001Sub000Block177Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part006] using hcert

def TailChunk001Sub000Block177Part007SupportExplicit : Finset ℕ :=
  ([23790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part007 : ℚ :=
  (20790792731 : ℚ) / 55048664619417600

def SurrogateDiagonalTailChunk001Sub000Block177Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23790
    = surrogateDiagTailX0RatChunk001Sub000Block177Part007

theorem surrogateDiagonalTailChunk001Sub000Block177Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part007] using hcert

def TailChunk001Sub000Block177Part008SupportExplicit : Finset ℕ :=
  ([23791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part008 : ℚ :=
  (217034101075 : ℚ) / 713472066046853203968

def SurrogateDiagonalTailChunk001Sub000Block177Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23791
    = surrogateDiagTailX0RatChunk001Sub000Block177Part008

theorem surrogateDiagonalTailChunk001Sub000Block177Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part008] using hcert

def TailChunk001Sub000Block177Part009SupportExplicit : Finset ℕ :=
  ([23793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part009 : ℚ :=
  (11289573079 : ℚ) / 748326744413798400

def SurrogateDiagonalTailChunk001Sub000Block177Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23793
    = surrogateDiagTailX0RatChunk001Sub000Block177Part009

theorem surrogateDiagonalTailChunk001Sub000Block177Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part009] using hcert

def TailChunk001Sub000Block177Part010SupportExplicit : Finset ℕ :=
  ([23794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block177Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23794
    = surrogateDiagTailX0RatChunk001Sub000Block177Part010

theorem surrogateDiagonalTailChunk001Sub000Block177Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part010] using hcert

def TailChunk001Sub000Block177Part011SupportExplicit : Finset ℕ :=
  ([23795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part011 : ℚ :=
  (1416160842625 : ℚ) / 328068531774779148288

def SurrogateDiagonalTailChunk001Sub000Block177Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23795
    = surrogateDiagTailX0RatChunk001Sub000Block177Part011

theorem surrogateDiagonalTailChunk001Sub000Block177Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part011] using hcert

def TailChunk001Sub000Block177Part012SupportExplicit : Finset ℕ :=
  ([23797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part012 : ℚ :=
  (22009524625 : ℚ) / 105209328665156911104

def SurrogateDiagonalTailChunk001Sub000Block177Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23797
    = surrogateDiagTailX0RatChunk001Sub000Block177Part012

theorem surrogateDiagonalTailChunk001Sub000Block177Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part012] using hcert

def TailChunk001Sub000Block177Part013SupportExplicit : Finset ℕ :=
  ([23798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part013 : ℚ :=
  (2699491075 : ℚ) / 1714167033633275904

def SurrogateDiagonalTailChunk001Sub000Block177Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23798
    = surrogateDiagTailX0RatChunk001Sub000Block177Part013

theorem surrogateDiagonalTailChunk001Sub000Block177Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part013] using hcert

def TailChunk001Sub000Block177Part014SupportExplicit : Finset ℕ :=
  ([23799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part014 : ℚ :=
  (41675 : ℚ) / 10556004201486336

def SurrogateDiagonalTailChunk001Sub000Block177Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23799
    = surrogateDiagTailX0RatChunk001Sub000Block177Part014

theorem surrogateDiagonalTailChunk001Sub000Block177Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part014] using hcert

def TailChunk001Sub000Block177Part015SupportExplicit : Finset ℕ :=
  ([23801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block177Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23801
    = surrogateDiagTailX0RatChunk001Sub000Block177Part015

theorem surrogateDiagonalTailChunk001Sub000Block177Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part015] using hcert

def TailChunk001Sub000Block177Part016SupportExplicit : Finset ℕ :=
  ([23802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part016 : ℚ :=
  (491848669175 : ℚ) / 4949116594840609344

def SurrogateDiagonalTailChunk001Sub000Block177Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23802
    = surrogateDiagTailX0RatChunk001Sub000Block177Part016

theorem surrogateDiagonalTailChunk001Sub000Block177Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part016] using hcert

def TailChunk001Sub000Block177Part017SupportExplicit : Finset ℕ :=
  ([23803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part017 : ℚ :=
  (625603487 : ℚ) / 861494341343385600

def SurrogateDiagonalTailChunk001Sub000Block177Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23803
    = surrogateDiagTailX0RatChunk001Sub000Block177Part017

theorem surrogateDiagonalTailChunk001Sub000Block177Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part017] using hcert

def TailChunk001Sub000Block177Part018SupportExplicit : Finset ℕ :=
  ([23806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block177Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23806
    = surrogateDiagTailX0RatChunk001Sub000Block177Part018

theorem surrogateDiagonalTailChunk001Sub000Block177Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part018] using hcert

def TailChunk001Sub000Block177Part019SupportExplicit : Finset ℕ :=
  ([23807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part019 : ℚ :=
  (1005661299925 : ℚ) / 341508792925602367488

def SurrogateDiagonalTailChunk001Sub000Block177Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23807
    = surrogateDiagTailX0RatChunk001Sub000Block177Part019

theorem surrogateDiagonalTailChunk001Sub000Block177Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part019] using hcert

def TailChunk001Sub000Block177Part020SupportExplicit : Finset ℕ :=
  ([23809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part020 : ℚ :=
  (10425195751 : ℚ) / 27795493238506291200

def SurrogateDiagonalTailChunk001Sub000Block177Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23809
    = surrogateDiagTailX0RatChunk001Sub000Block177Part020

theorem surrogateDiagonalTailChunk001Sub000Block177Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part020] using hcert

def TailChunk001Sub000Block177Part021SupportExplicit : Finset ℕ :=
  ([23810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part021 : ℚ :=
  (12142269777 : ℚ) / 39121486562099200

def SurrogateDiagonalTailChunk001Sub000Block177Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23810
    = surrogateDiagTailX0RatChunk001Sub000Block177Part021

theorem surrogateDiagonalTailChunk001Sub000Block177Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part021] using hcert

def TailChunk001Sub000Block177Part022SupportExplicit : Finset ℕ :=
  ([23811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part022 : ℚ :=
  (15745648206325 : ℚ) / 158691431626705993728

def SurrogateDiagonalTailChunk001Sub000Block177Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23811
    = surrogateDiagTailX0RatChunk001Sub000Block177Part022

theorem surrogateDiagonalTailChunk001Sub000Block177Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part022] using hcert

def TailChunk001Sub000Block177Part023SupportExplicit : Finset ℕ :=
  ([23813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part023 : ℚ :=
  (8860296390625 : ℚ) / 200978852873457045792

def SurrogateDiagonalTailChunk001Sub000Block177Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23813
    = surrogateDiagTailX0RatChunk001Sub000Block177Part023

theorem surrogateDiagonalTailChunk001Sub000Block177Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part023] using hcert

def TailChunk001Sub000Block177Part024SupportExplicit : Finset ℕ :=
  ([23815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block177Part024 : ℚ :=
  (81238858009 : ℚ) / 891788366834565120

def SurrogateDiagonalTailChunk001Sub000Block177Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23815
    = surrogateDiagTailX0RatChunk001Sub000Block177Part024

theorem surrogateDiagonalTailChunk001Sub000Block177Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block177Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block177Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block177Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block177Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block177Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block177HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block177Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block177Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block177Part000
    + surrogateDiagTailX0RatChunk001Sub000Block177Part001
    + surrogateDiagTailX0RatChunk001Sub000Block177Part002
    + surrogateDiagTailX0RatChunk001Sub000Block177Part003
    + surrogateDiagTailX0RatChunk001Sub000Block177Part004
    + surrogateDiagTailX0RatChunk001Sub000Block177Part005
    + surrogateDiagTailX0RatChunk001Sub000Block177Part006
    + surrogateDiagTailX0RatChunk001Sub000Block177Part007
    + surrogateDiagTailX0RatChunk001Sub000Block177Part008
    + surrogateDiagTailX0RatChunk001Sub000Block177Part009

def surrogateDiagonalTailChunk001Sub000Block177MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block177Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block177Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block177Part010
    + surrogateDiagTailX0RatChunk001Sub000Block177Part011
    + surrogateDiagTailX0RatChunk001Sub000Block177Part012
    + surrogateDiagTailX0RatChunk001Sub000Block177Part013
    + surrogateDiagTailX0RatChunk001Sub000Block177Part014
    + surrogateDiagTailX0RatChunk001Sub000Block177Part015
    + surrogateDiagTailX0RatChunk001Sub000Block177Part016
    + surrogateDiagTailX0RatChunk001Sub000Block177Part017
    + surrogateDiagTailX0RatChunk001Sub000Block177Part018
    + surrogateDiagTailX0RatChunk001Sub000Block177Part019

def surrogateDiagonalTailChunk001Sub000Block177TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block177Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block177Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block177Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block177Part020
    + surrogateDiagTailX0RatChunk001Sub000Block177Part021
    + surrogateDiagTailX0RatChunk001Sub000Block177Part022
    + surrogateDiagTailX0RatChunk001Sub000Block177Part023
    + surrogateDiagTailX0RatChunk001Sub000Block177Part024

def surrogateDiagonalTailChunk001Sub000Block177Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block177HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block177MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block177TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block177 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block177Part000
    + surrogateDiagTailX0RatChunk001Sub000Block177Part001
    + surrogateDiagTailX0RatChunk001Sub000Block177Part002
    + surrogateDiagTailX0RatChunk001Sub000Block177Part003
    + surrogateDiagTailX0RatChunk001Sub000Block177Part004
    + surrogateDiagTailX0RatChunk001Sub000Block177Part005
    + surrogateDiagTailX0RatChunk001Sub000Block177Part006
    + surrogateDiagTailX0RatChunk001Sub000Block177Part007
    + surrogateDiagTailX0RatChunk001Sub000Block177Part008
    + surrogateDiagTailX0RatChunk001Sub000Block177Part009
    + surrogateDiagTailX0RatChunk001Sub000Block177Part010
    + surrogateDiagTailX0RatChunk001Sub000Block177Part011
    + surrogateDiagTailX0RatChunk001Sub000Block177Part012
    + surrogateDiagTailX0RatChunk001Sub000Block177Part013
    + surrogateDiagTailX0RatChunk001Sub000Block177Part014
    + surrogateDiagTailX0RatChunk001Sub000Block177Part015
    + surrogateDiagTailX0RatChunk001Sub000Block177Part016
    + surrogateDiagTailX0RatChunk001Sub000Block177Part017
    + surrogateDiagTailX0RatChunk001Sub000Block177Part018
    + surrogateDiagTailX0RatChunk001Sub000Block177Part019
    + surrogateDiagTailX0RatChunk001Sub000Block177Part020
    + surrogateDiagTailX0RatChunk001Sub000Block177Part021
    + surrogateDiagTailX0RatChunk001Sub000Block177Part022
    + surrogateDiagTailX0RatChunk001Sub000Block177Part023
    + surrogateDiagTailX0RatChunk001Sub000Block177Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block177_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block177Head + surrogateDiagTailX0RatChunk001Sub000Block177Mid + surrogateDiagTailX0RatChunk001Sub000Block177Tail =
      surrogateDiagTailX0RatChunk001Sub000Block177 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block177Head surrogateDiagTailX0RatChunk001Sub000Block177Mid surrogateDiagTailX0RatChunk001Sub000Block177Tail surrogateDiagTailX0RatChunk001Sub000Block177
  ring

def SurrogateDiagonalTailChunk001Sub000Block177HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block177HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block177Head

def SurrogateDiagonalTailChunk001Sub000Block177MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block177MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block177Mid

def SurrogateDiagonalTailChunk001Sub000Block177TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block177TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block177Tail

theorem surrogateDiagonalTailChunk001Sub000Block177_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block177HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block177MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block177TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block177Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block177 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block177HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block177MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block177TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block177Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block177_eq_head_add_mid_add_tail

/-- Block 178 covers tail-support indices [14450,14475) and q from 23817 to 23858. -/

def TailChunk001Sub000Block178Part000SupportExplicit : Finset ℕ :=
  ([23817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part000 : ℚ :=
  (4721884119525 : ℚ) / 41214419211969888256

def SurrogateDiagonalTailChunk001Sub000Block178Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23817
    = surrogateDiagTailX0RatChunk001Sub000Block178Part000

theorem surrogateDiagonalTailChunk001Sub000Block178Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part000] using hcert

def TailChunk001Sub000Block178Part001SupportExplicit : Finset ℕ :=
  ([23818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part001 : ℚ :=
  (2216004390625 : ℚ) / 12569620665583386912

def SurrogateDiagonalTailChunk001Sub000Block178Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23818
    = surrogateDiagTailX0RatChunk001Sub000Block178Part001

theorem surrogateDiagonalTailChunk001Sub000Block178Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part001] using hcert

def TailChunk001Sub000Block178Part002SupportExplicit : Finset ℕ :=
  ([23819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part002 : ℚ :=
  (8864761890625 : ℚ) / 201181495065031943922

def SurrogateDiagonalTailChunk001Sub000Block178Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23819
    = surrogateDiagTailX0RatChunk001Sub000Block178Part002

theorem surrogateDiagonalTailChunk001Sub000Block178Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part002] using hcert

def TailChunk001Sub000Block178Part003SupportExplicit : Finset ℕ :=
  ([23821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part003 : ℚ :=
  (501842138363 : ℚ) / 7501657483778457600

def SurrogateDiagonalTailChunk001Sub000Block178Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23821
    = surrogateDiagTailX0RatChunk001Sub000Block178Part003

theorem surrogateDiagonalTailChunk001Sub000Block178Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part003] using hcert

def TailChunk001Sub000Block178Part004SupportExplicit : Finset ℕ :=
  ([23822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part004 : ℚ :=
  (8493538411525 : ℚ) / 45150269686505883648

def SurrogateDiagonalTailChunk001Sub000Block178Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23822
    = surrogateDiagTailX0RatChunk001Sub000Block178Part004

theorem surrogateDiagonalTailChunk001Sub000Block178Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part004] using hcert

def TailChunk001Sub000Block178Part005SupportExplicit : Finset ℕ :=
  ([23827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part005 : ℚ :=
  (8870717640625 : ℚ) / 201451922979587901522

def SurrogateDiagonalTailChunk001Sub000Block178Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23827
    = surrogateDiagTailX0RatChunk001Sub000Block178Part005

theorem surrogateDiagonalTailChunk001Sub000Block178Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part005] using hcert

def TailChunk001Sub000Block178Part006SupportExplicit : Finset ℕ :=
  ([23830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part006 : ℚ :=
  (6030362008525 : ℚ) / 20607905433912035328

def SurrogateDiagonalTailChunk001Sub000Block178Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23830
    = surrogateDiagTailX0RatChunk001Sub000Block178Part006

theorem surrogateDiagonalTailChunk001Sub000Block178Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part006] using hcert

def TailChunk001Sub000Block178Part007SupportExplicit : Finset ℕ :=
  ([23831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part007 : ℚ :=
  (14197914025 : ℚ) / 322539582604727442

def SurrogateDiagonalTailChunk001Sub000Block178Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23831
    = surrogateDiagTailX0RatChunk001Sub000Block178Part007

theorem surrogateDiagonalTailChunk001Sub000Block178Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part007] using hcert

def TailChunk001Sub000Block178Part008SupportExplicit : Finset ℕ :=
  ([23833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part008 : ℚ :=
  (8875185765625 : ℚ) / 201654922759919350272

def SurrogateDiagonalTailChunk001Sub000Block178Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23833
    = surrogateDiagTailX0RatChunk001Sub000Block178Part008

theorem surrogateDiagonalTailChunk001Sub000Block178Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part008] using hcert

def TailChunk001Sub000Block178Part009SupportExplicit : Finset ℕ :=
  ([23834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part009 : ℚ :=
  (32118891127 : ℚ) / 157383406387200000

def SurrogateDiagonalTailChunk001Sub000Block178Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23834
    = surrogateDiagTailX0RatChunk001Sub000Block178Part009

theorem surrogateDiagonalTailChunk001Sub000Block178Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part009] using hcert

def TailChunk001Sub000Block178Part010SupportExplicit : Finset ℕ :=
  ([23835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part010 : ℚ :=
  (8004460278475 : ℚ) / 34627852981366161408

def SurrogateDiagonalTailChunk001Sub000Block178Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23835
    = surrogateDiagTailX0RatChunk001Sub000Block178Part010

theorem surrogateDiagonalTailChunk001Sub000Block178Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part010] using hcert

def TailChunk001Sub000Block178Part011SupportExplicit : Finset ℕ :=
  ([23838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part011 : ℚ :=
  (4628000753875 : ℚ) / 8412684470313811968

def SurrogateDiagonalTailChunk001Sub000Block178Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23838
    = surrogateDiagTailX0RatChunk001Sub000Block178Part011

theorem surrogateDiagonalTailChunk001Sub000Block178Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part011] using hcert

def TailChunk001Sub000Block178Part012SupportExplicit : Finset ℕ :=
  ([23839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part012 : ℚ :=
  (266986172933 : ℚ) / 5636983257028362240

def SurrogateDiagonalTailChunk001Sub000Block178Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23839
    = surrogateDiagTailX0RatChunk001Sub000Block178Part012

theorem surrogateDiagonalTailChunk001Sub000Block178Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part012] using hcert

def TailChunk001Sub000Block178Part013SupportExplicit : Finset ℕ :=
  ([23842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part013 : ℚ :=
  (47898879017 : ℚ) / 153539542011248640

def SurrogateDiagonalTailChunk001Sub000Block178Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23842
    = surrogateDiagTailX0RatChunk001Sub000Block178Part013

theorem surrogateDiagonalTailChunk001Sub000Block178Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part013] using hcert

def TailChunk001Sub000Block178Part014SupportExplicit : Finset ℕ :=
  ([23843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part014 : ℚ :=
  (346751637943 : ℚ) / 7652020564397260800

def SurrogateDiagonalTailChunk001Sub000Block178Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23843
    = surrogateDiagTailX0RatChunk001Sub000Block178Part014

theorem surrogateDiagonalTailChunk001Sub000Block178Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part014] using hcert

def TailChunk001Sub000Block178Part015SupportExplicit : Finset ℕ :=
  ([23845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part015 : ℚ :=
  (820708699081 : ℚ) / 10499699520000000000

def SurrogateDiagonalTailChunk001Sub000Block178Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23845
    = surrogateDiagTailX0RatChunk001Sub000Block178Part015

theorem surrogateDiagonalTailChunk001Sub000Block178Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part015] using hcert

def TailChunk001Sub000Block178Part016SupportExplicit : Finset ℕ :=
  ([23846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part016 : ℚ :=
  (2221217640625 : ℚ) / 12628836408803724882

def SurrogateDiagonalTailChunk001Sub000Block178Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23846
    = surrogateDiagTailX0RatChunk001Sub000Block178Part016

theorem surrogateDiagonalTailChunk001Sub000Block178Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part016] using hcert

def TailChunk001Sub000Block178Part017SupportExplicit : Finset ℕ :=
  ([23847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part017 : ℚ :=
  (15793300205125 : ℚ) / 159653438056975484928

def SurrogateDiagonalTailChunk001Sub000Block178Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23847
    = surrogateDiagTailX0RatChunk001Sub000Block178Part017

theorem surrogateDiagonalTailChunk001Sub000Block178Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part017] using hcert

def TailChunk001Sub000Block178Part018SupportExplicit : Finset ℕ :=
  ([23849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part018 : ℚ :=
  (26830542468025 : ℚ) / 436124450160965524608

def SurrogateDiagonalTailChunk001Sub000Block178Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23849
    = surrogateDiagTailX0RatChunk001Sub000Block178Part018

theorem surrogateDiagonalTailChunk001Sub000Block178Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part018] using hcert

def TailChunk001Sub000Block178Part019SupportExplicit : Finset ℕ :=
  ([23851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part019 : ℚ :=
  (227122709201 : ℚ) / 3980086413298237440

def SurrogateDiagonalTailChunk001Sub000Block178Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23851
    = surrogateDiagTailX0RatChunk001Sub000Block178Part019

theorem surrogateDiagonalTailChunk001Sub000Block178Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part019] using hcert

def TailChunk001Sub000Block178Part020SupportExplicit : Finset ℕ :=
  ([23853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part020 : ℚ :=
  (632049968197 : ℚ) / 6392567867922000000

def SurrogateDiagonalTailChunk001Sub000Block178Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23853
    = surrogateDiagTailX0RatChunk001Sub000Block178Part020

theorem surrogateDiagonalTailChunk001Sub000Block178Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part020] using hcert

def TailChunk001Sub000Block178Part021SupportExplicit : Finset ℕ :=
  ([23854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part021 : ℚ :=
  (2222708265625 : ℚ) / 12645793555002014322

def SurrogateDiagonalTailChunk001Sub000Block178Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23854
    = surrogateDiagTailX0RatChunk001Sub000Block178Part021

theorem surrogateDiagonalTailChunk001Sub000Block178Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part021] using hcert

def TailChunk001Sub000Block178Part022SupportExplicit : Finset ℕ :=
  ([23855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part022 : ℚ :=
  (9832045386125 : ℚ) / 119092977747309625344

def SurrogateDiagonalTailChunk001Sub000Block178Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23855
    = surrogateDiagTailX0RatChunk001Sub000Block178Part022

theorem surrogateDiagonalTailChunk001Sub000Block178Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part022] using hcert

def TailChunk001Sub000Block178Part023SupportExplicit : Finset ℕ :=
  ([23857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part023 : ℚ :=
  (8893069515625 : ℚ) / 202468456463872499712

def SurrogateDiagonalTailChunk001Sub000Block178Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23857
    = surrogateDiagTailX0RatChunk001Sub000Block178Part023

theorem surrogateDiagonalTailChunk001Sub000Block178Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part023] using hcert

def TailChunk001Sub000Block178Part024SupportExplicit : Finset ℕ :=
  ([23858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block178Part024 : ℚ :=
  (345024990607 : ℚ) / 1874261987442000000

def SurrogateDiagonalTailChunk001Sub000Block178Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23858
    = surrogateDiagTailX0RatChunk001Sub000Block178Part024

theorem surrogateDiagonalTailChunk001Sub000Block178Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block178Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block178Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block178Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block178Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block178Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block178HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block178Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block178Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block178Part000
    + surrogateDiagTailX0RatChunk001Sub000Block178Part001
    + surrogateDiagTailX0RatChunk001Sub000Block178Part002
    + surrogateDiagTailX0RatChunk001Sub000Block178Part003
    + surrogateDiagTailX0RatChunk001Sub000Block178Part004
    + surrogateDiagTailX0RatChunk001Sub000Block178Part005
    + surrogateDiagTailX0RatChunk001Sub000Block178Part006
    + surrogateDiagTailX0RatChunk001Sub000Block178Part007
    + surrogateDiagTailX0RatChunk001Sub000Block178Part008
    + surrogateDiagTailX0RatChunk001Sub000Block178Part009

def surrogateDiagonalTailChunk001Sub000Block178MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block178Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block178Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block178Part010
    + surrogateDiagTailX0RatChunk001Sub000Block178Part011
    + surrogateDiagTailX0RatChunk001Sub000Block178Part012
    + surrogateDiagTailX0RatChunk001Sub000Block178Part013
    + surrogateDiagTailX0RatChunk001Sub000Block178Part014
    + surrogateDiagTailX0RatChunk001Sub000Block178Part015
    + surrogateDiagTailX0RatChunk001Sub000Block178Part016
    + surrogateDiagTailX0RatChunk001Sub000Block178Part017
    + surrogateDiagTailX0RatChunk001Sub000Block178Part018
    + surrogateDiagTailX0RatChunk001Sub000Block178Part019

def surrogateDiagonalTailChunk001Sub000Block178TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block178Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block178Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block178Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block178Part020
    + surrogateDiagTailX0RatChunk001Sub000Block178Part021
    + surrogateDiagTailX0RatChunk001Sub000Block178Part022
    + surrogateDiagTailX0RatChunk001Sub000Block178Part023
    + surrogateDiagTailX0RatChunk001Sub000Block178Part024

def surrogateDiagonalTailChunk001Sub000Block178Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block178HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block178MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block178TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block178 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block178Part000
    + surrogateDiagTailX0RatChunk001Sub000Block178Part001
    + surrogateDiagTailX0RatChunk001Sub000Block178Part002
    + surrogateDiagTailX0RatChunk001Sub000Block178Part003
    + surrogateDiagTailX0RatChunk001Sub000Block178Part004
    + surrogateDiagTailX0RatChunk001Sub000Block178Part005
    + surrogateDiagTailX0RatChunk001Sub000Block178Part006
    + surrogateDiagTailX0RatChunk001Sub000Block178Part007
    + surrogateDiagTailX0RatChunk001Sub000Block178Part008
    + surrogateDiagTailX0RatChunk001Sub000Block178Part009
    + surrogateDiagTailX0RatChunk001Sub000Block178Part010
    + surrogateDiagTailX0RatChunk001Sub000Block178Part011
    + surrogateDiagTailX0RatChunk001Sub000Block178Part012
    + surrogateDiagTailX0RatChunk001Sub000Block178Part013
    + surrogateDiagTailX0RatChunk001Sub000Block178Part014
    + surrogateDiagTailX0RatChunk001Sub000Block178Part015
    + surrogateDiagTailX0RatChunk001Sub000Block178Part016
    + surrogateDiagTailX0RatChunk001Sub000Block178Part017
    + surrogateDiagTailX0RatChunk001Sub000Block178Part018
    + surrogateDiagTailX0RatChunk001Sub000Block178Part019
    + surrogateDiagTailX0RatChunk001Sub000Block178Part020
    + surrogateDiagTailX0RatChunk001Sub000Block178Part021
    + surrogateDiagTailX0RatChunk001Sub000Block178Part022
    + surrogateDiagTailX0RatChunk001Sub000Block178Part023
    + surrogateDiagTailX0RatChunk001Sub000Block178Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block178_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block178Head + surrogateDiagTailX0RatChunk001Sub000Block178Mid + surrogateDiagTailX0RatChunk001Sub000Block178Tail =
      surrogateDiagTailX0RatChunk001Sub000Block178 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block178Head surrogateDiagTailX0RatChunk001Sub000Block178Mid surrogateDiagTailX0RatChunk001Sub000Block178Tail surrogateDiagTailX0RatChunk001Sub000Block178
  ring

def SurrogateDiagonalTailChunk001Sub000Block178HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block178HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block178Head

def SurrogateDiagonalTailChunk001Sub000Block178MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block178MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block178Mid

def SurrogateDiagonalTailChunk001Sub000Block178TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block178TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block178Tail

theorem surrogateDiagonalTailChunk001Sub000Block178_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block178HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block178MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block178TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block178Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block178 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block178HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block178MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block178TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block178Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block178_eq_head_add_mid_add_tail

/-- Block 179 covers tail-support indices [14475,14500) and q from 23861 to 23899. -/

def TailChunk001Sub000Block179Part000SupportExplicit : Finset ℕ :=
  ([23861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part000 : ℚ :=
  (2892454130675 : ℚ) / 63897074068867005024

def SurrogateDiagonalTailChunk001Sub000Block179Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23861
    = surrogateDiagTailX0RatChunk001Sub000Block179Part000

theorem surrogateDiagonalTailChunk001Sub000Block179Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part000] using hcert

def TailChunk001Sub000Block179Part001SupportExplicit : Finset ℕ :=
  ([23862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part001 : ℚ :=
  (25118363713 : ℚ) / 57993654907699200

def SurrogateDiagonalTailChunk001Sub000Block179Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23862
    = surrogateDiagTailX0RatChunk001Sub000Block179Part001

theorem surrogateDiagonalTailChunk001Sub000Block179Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part001] using hcert

def TailChunk001Sub000Block179Part002SupportExplicit : Finset ℕ :=
  ([23865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part002 : ℚ :=
  (9604733742925 : ℚ) / 53529596719244771328

def SurrogateDiagonalTailChunk001Sub000Block179Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23865
    = surrogateDiagTailX0RatChunk001Sub000Block179Part002

theorem surrogateDiagonalTailChunk001Sub000Block179Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part002] using hcert

def TailChunk001Sub000Block179Part003SupportExplicit : Finset ℕ :=
  ([23866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part003 : ℚ :=
  (2224945140625 : ℚ) / 12671261285911440672

def SurrogateDiagonalTailChunk001Sub000Block179Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23866
    = surrogateDiagTailX0RatChunk001Sub000Block179Part003

theorem surrogateDiagonalTailChunk001Sub000Block179Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part003] using hcert

def TailChunk001Sub000Block179Part004SupportExplicit : Finset ℕ :=
  ([23867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part004 : ℚ :=
  (925848011875 : ℚ) / 19491432293130674688

def SurrogateDiagonalTailChunk001Sub000Block179Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23867
    = surrogateDiagTailX0RatChunk001Sub000Block179Part004

theorem surrogateDiagonalTailChunk001Sub000Block179Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part004] using hcert

def TailChunk001Sub000Block179Part005SupportExplicit : Finset ℕ :=
  ([23869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part005 : ℚ :=
  (8902018140625 : ℚ) / 202876145147273693472

def SurrogateDiagonalTailChunk001Sub000Block179Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23869
    = surrogateDiagTailX0RatChunk001Sub000Block179Part005

theorem surrogateDiagonalTailChunk001Sub000Block179Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part005] using hcert

def TailChunk001Sub000Block179Part006SupportExplicit : Finset ℕ :=
  ([23870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part006 : ℚ :=
  (438092093 : ℚ) / 746645299200000

def SurrogateDiagonalTailChunk001Sub000Block179Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23870
    = surrogateDiagTailX0RatChunk001Sub000Block179Part006

theorem surrogateDiagonalTailChunk001Sub000Block179Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part006] using hcert

def TailChunk001Sub000Block179Part007SupportExplicit : Finset ℕ :=
  ([23871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part007 : ℚ :=
  (7611237447575 : ℚ) / 73137793435019771904

def SurrogateDiagonalTailChunk001Sub000Block179Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23871
    = surrogateDiagTailX0RatChunk001Sub000Block179Part007

theorem surrogateDiagonalTailChunk001Sub000Block179Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part007] using hcert

def TailChunk001Sub000Block179Part008SupportExplicit : Finset ℕ :=
  ([23873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part008 : ℚ :=
  (8905002015625 : ℚ) / 203012178095407890432

def SurrogateDiagonalTailChunk001Sub000Block179Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23873
    = surrogateDiagTailX0RatChunk001Sub000Block179Part008

theorem surrogateDiagonalTailChunk001Sub000Block179Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part008] using hcert

def TailChunk001Sub000Block179Part009SupportExplicit : Finset ℕ :=
  ([23874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part009 : ℚ :=
  (335900709125 : ℚ) / 745690597920964608

def SurrogateDiagonalTailChunk001Sub000Block179Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23874
    = surrogateDiagTailX0RatChunk001Sub000Block179Part009

theorem surrogateDiagonalTailChunk001Sub000Block179Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part009] using hcert

def TailChunk001Sub000Block179Part010SupportExplicit : Finset ℕ :=
  ([23878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part010 : ℚ :=
  (2227183140625 : ℚ) / 12696767465119089042

def SurrogateDiagonalTailChunk001Sub000Block179Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23878
    = surrogateDiagTailX0RatChunk001Sub000Block179Part010

theorem surrogateDiagonalTailChunk001Sub000Block179Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part010] using hcert

def TailChunk001Sub000Block179Part011SupportExplicit : Finset ℕ :=
  ([23879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part011 : ℚ :=
  (8909478765625 : ℚ) / 203216355771703925682

def SurrogateDiagonalTailChunk001Sub000Block179Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23879
    = surrogateDiagTailX0RatChunk001Sub000Block179Part011

theorem surrogateDiagonalTailChunk001Sub000Block179Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part011] using hcert

def TailChunk001Sub000Block179Part012SupportExplicit : Finset ℕ :=
  ([23881] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part012 : ℚ :=
  (337356345917 : ℚ) / 5249560338159206400

def SurrogateDiagonalTailChunk001Sub000Block179Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23881
    = surrogateDiagTailX0RatChunk001Sub000Block179Part012

theorem surrogateDiagonalTailChunk001Sub000Block179Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part012] using hcert

def TailChunk001Sub000Block179Part013SupportExplicit : Finset ℕ :=
  ([23882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part013 : ℚ :=
  (3564687025 : ℚ) / 20328444920968992

def SurrogateDiagonalTailChunk001Sub000Block179Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23882
    = surrogateDiagTailX0RatChunk001Sub000Block179Part013

theorem surrogateDiagonalTailChunk001Sub000Block179Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part013] using hcert

def TailChunk001Sub000Block179Part014SupportExplicit : Finset ℕ :=
  ([23883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part014 : ℚ :=
  (4793981938675 : ℚ) / 42738643553530484736

def SurrogateDiagonalTailChunk001Sub000Block179Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23883
    = surrogateDiagTailX0RatChunk001Sub000Block179Part014

theorem surrogateDiagonalTailChunk001Sub000Block179Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part014] using hcert

def TailChunk001Sub000Block179Part015SupportExplicit : Finset ℕ :=
  ([23885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part015 : ℚ :=
  (815750673307 : ℚ) / 10314278920991539200

def SurrogateDiagonalTailChunk001Sub000Block179Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23885
    = surrogateDiagTailX0RatChunk001Sub000Block179Part015

theorem surrogateDiagonalTailChunk001Sub000Block179Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part015] using hcert

def TailChunk001Sub000Block179Part016SupportExplicit : Finset ℕ :=
  ([23887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part016 : ℚ :=
  (8915449515625 : ℚ) / 203488832201434594002

def SurrogateDiagonalTailChunk001Sub000Block179Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23887
    = surrogateDiagTailX0RatChunk001Sub000Block179Part016

theorem surrogateDiagonalTailChunk001Sub000Block179Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part016] using hcert

def TailChunk001Sub000Block179Part017SupportExplicit : Finset ℕ :=
  ([23889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part017 : ℚ :=
  (15848985203725 : ℚ) / 160781299517182889088

def SurrogateDiagonalTailChunk001Sub000Block179Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23889
    = surrogateDiagTailX0RatChunk001Sub000Block179Part017

theorem surrogateDiagonalTailChunk001Sub000Block179Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part017] using hcert

def TailChunk001Sub000Block179Part018SupportExplicit : Finset ℕ :=
  ([23890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part018 : ℚ :=
  (6060773620975 : ℚ) / 20816327599072247808

def SurrogateDiagonalTailChunk001Sub000Block179Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23890
    = surrogateDiagTailX0RatChunk001Sub000Block179Part018

theorem surrogateDiagonalTailChunk001Sub000Block179Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part018] using hcert

def TailChunk001Sub000Block179Part019SupportExplicit : Finset ℕ :=
  ([23891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part019 : ℚ :=
  (2910643550525 : ℚ) / 48800631384794990592

def SurrogateDiagonalTailChunk001Sub000Block179Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23891
    = surrogateDiagTailX0RatChunk001Sub000Block179Part019

theorem surrogateDiagonalTailChunk001Sub000Block179Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part019] using hcert

def TailChunk001Sub000Block179Part020SupportExplicit : Finset ℕ :=
  ([23893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part020 : ℚ :=
  (8919928890625 : ℚ) / 203693369270059022112

def SurrogateDiagonalTailChunk001Sub000Block179Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23893
    = surrogateDiagTailX0RatChunk001Sub000Block179Part020

theorem surrogateDiagonalTailChunk001Sub000Block179Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part020] using hcert

def TailChunk001Sub000Block179Part021SupportExplicit : Finset ℕ :=
  ([23894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part021 : ℚ :=
  (3899913062225 : ℚ) / 18411644137870992384

def SurrogateDiagonalTailChunk001Sub000Block179Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23894
    = surrogateDiagTailX0RatChunk001Sub000Block179Part021

theorem surrogateDiagonalTailChunk001Sub000Block179Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part021] using hcert

def TailChunk001Sub000Block179Part022SupportExplicit : Finset ℕ :=
  ([23897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part022 : ℚ :=
  (16435535894075 : ℚ) / 339998499628388656704

def SurrogateDiagonalTailChunk001Sub000Block179Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23897
    = surrogateDiagTailX0RatChunk001Sub000Block179Part022

theorem surrogateDiagonalTailChunk001Sub000Block179Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part022] using hcert

def TailChunk001Sub000Block179Part023SupportExplicit : Finset ℕ :=
  ([23898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part023 : ℚ :=
  (1594747857875 : ℚ) / 2698455063241949184

def SurrogateDiagonalTailChunk001Sub000Block179Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23898
    = surrogateDiagTailX0RatChunk001Sub000Block179Part023

theorem surrogateDiagonalTailChunk001Sub000Block179Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part023] using hcert

def TailChunk001Sub000Block179Part024SupportExplicit : Finset ℕ :=
  ([23899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block179Part024 : ℚ :=
  (8924409390625 : ℚ) / 203898060492979044402

def SurrogateDiagonalTailChunk001Sub000Block179Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 23899
    = surrogateDiagTailX0RatChunk001Sub000Block179Part024

theorem surrogateDiagonalTailChunk001Sub000Block179Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block179Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block179Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block179Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block179Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block179Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block179HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block179Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block179Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block179Part000
    + surrogateDiagTailX0RatChunk001Sub000Block179Part001
    + surrogateDiagTailX0RatChunk001Sub000Block179Part002
    + surrogateDiagTailX0RatChunk001Sub000Block179Part003
    + surrogateDiagTailX0RatChunk001Sub000Block179Part004
    + surrogateDiagTailX0RatChunk001Sub000Block179Part005
    + surrogateDiagTailX0RatChunk001Sub000Block179Part006
    + surrogateDiagTailX0RatChunk001Sub000Block179Part007
    + surrogateDiagTailX0RatChunk001Sub000Block179Part008
    + surrogateDiagTailX0RatChunk001Sub000Block179Part009

def surrogateDiagonalTailChunk001Sub000Block179MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block179Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block179Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block179Part010
    + surrogateDiagTailX0RatChunk001Sub000Block179Part011
    + surrogateDiagTailX0RatChunk001Sub000Block179Part012
    + surrogateDiagTailX0RatChunk001Sub000Block179Part013
    + surrogateDiagTailX0RatChunk001Sub000Block179Part014
    + surrogateDiagTailX0RatChunk001Sub000Block179Part015
    + surrogateDiagTailX0RatChunk001Sub000Block179Part016
    + surrogateDiagTailX0RatChunk001Sub000Block179Part017
    + surrogateDiagTailX0RatChunk001Sub000Block179Part018
    + surrogateDiagTailX0RatChunk001Sub000Block179Part019

def surrogateDiagonalTailChunk001Sub000Block179TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block179Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block179Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block179Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block179Part020
    + surrogateDiagTailX0RatChunk001Sub000Block179Part021
    + surrogateDiagTailX0RatChunk001Sub000Block179Part022
    + surrogateDiagTailX0RatChunk001Sub000Block179Part023
    + surrogateDiagTailX0RatChunk001Sub000Block179Part024

def surrogateDiagonalTailChunk001Sub000Block179Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block179HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block179MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block179TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block179 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block179Part000
    + surrogateDiagTailX0RatChunk001Sub000Block179Part001
    + surrogateDiagTailX0RatChunk001Sub000Block179Part002
    + surrogateDiagTailX0RatChunk001Sub000Block179Part003
    + surrogateDiagTailX0RatChunk001Sub000Block179Part004
    + surrogateDiagTailX0RatChunk001Sub000Block179Part005
    + surrogateDiagTailX0RatChunk001Sub000Block179Part006
    + surrogateDiagTailX0RatChunk001Sub000Block179Part007
    + surrogateDiagTailX0RatChunk001Sub000Block179Part008
    + surrogateDiagTailX0RatChunk001Sub000Block179Part009
    + surrogateDiagTailX0RatChunk001Sub000Block179Part010
    + surrogateDiagTailX0RatChunk001Sub000Block179Part011
    + surrogateDiagTailX0RatChunk001Sub000Block179Part012
    + surrogateDiagTailX0RatChunk001Sub000Block179Part013
    + surrogateDiagTailX0RatChunk001Sub000Block179Part014
    + surrogateDiagTailX0RatChunk001Sub000Block179Part015
    + surrogateDiagTailX0RatChunk001Sub000Block179Part016
    + surrogateDiagTailX0RatChunk001Sub000Block179Part017
    + surrogateDiagTailX0RatChunk001Sub000Block179Part018
    + surrogateDiagTailX0RatChunk001Sub000Block179Part019
    + surrogateDiagTailX0RatChunk001Sub000Block179Part020
    + surrogateDiagTailX0RatChunk001Sub000Block179Part021
    + surrogateDiagTailX0RatChunk001Sub000Block179Part022
    + surrogateDiagTailX0RatChunk001Sub000Block179Part023
    + surrogateDiagTailX0RatChunk001Sub000Block179Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block179_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block179Head + surrogateDiagTailX0RatChunk001Sub000Block179Mid + surrogateDiagTailX0RatChunk001Sub000Block179Tail =
      surrogateDiagTailX0RatChunk001Sub000Block179 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block179Head surrogateDiagTailX0RatChunk001Sub000Block179Mid surrogateDiagTailX0RatChunk001Sub000Block179Tail surrogateDiagTailX0RatChunk001Sub000Block179
  ring

def SurrogateDiagonalTailChunk001Sub000Block179HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block179HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block179Head

def SurrogateDiagonalTailChunk001Sub000Block179MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block179MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block179Mid

def SurrogateDiagonalTailChunk001Sub000Block179TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block179TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block179Tail

theorem surrogateDiagonalTailChunk001Sub000Block179_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block179HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block179MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block179TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block179Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block179 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block179HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block179MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block179TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block179Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block179_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
