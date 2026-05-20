import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [155,156). -/

/- Block 155 covers tail-support indices [3875,3900) and q from 6429 to 6466. -/

def TailChunk000Sub000Block155Part000SupportExplicit : Finset ℕ :=
  ([6429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part000 : ℚ :=
  (358663885525 : ℚ) / 210554591406741792

def SurrogateDiagonalTailChunk000Sub000Block155Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6429
    = surrogateDiagTailX0RatChunk000Sub000Block155Part000

theorem surrogateDiagonalTailChunk000Sub000Block155Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part000] using hcert

def TailChunk000Sub000Block155Part001SupportExplicit : Finset ℕ :=
  ([6430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part001 : ℚ :=
  (980313608575 : ℚ) / 108744408786290688

def SurrogateDiagonalTailChunk000Sub000Block155Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6430
    = surrogateDiagTailX0RatChunk000Sub000Block155Part001

theorem surrogateDiagonalTailChunk000Sub000Block155Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part001] using hcert

def TailChunk000Sub000Block155Part002SupportExplicit : Finset ℕ :=
  ([6431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part002 : ℚ :=
  (2503602457675 : ℚ) / 3849761766864734208

def SurrogateDiagonalTailChunk000Sub000Block155Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6431
    = surrogateDiagTailX0RatChunk000Sub000Block155Part002

theorem surrogateDiagonalTailChunk000Sub000Block155Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part002] using hcert

def TailChunk000Sub000Block155Part003SupportExplicit : Finset ℕ :=
  ([6433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part003 : ℚ :=
  (124062429875 : ℚ) / 135379736307874944

def SurrogateDiagonalTailChunk000Sub000Block155Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6433
    = surrogateDiagTailX0RatChunk000Sub000Block155Part003

theorem surrogateDiagonalTailChunk000Sub000Block155Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part003] using hcert

def TailChunk000Sub000Block155Part004SupportExplicit : Finset ℕ :=
  ([6434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part004 : ℚ :=
  (161704515625 : ℚ) / 66869954525601792

def SurrogateDiagonalTailChunk000Sub000Block155Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6434
    = surrogateDiagTailX0RatChunk000Sub000Block155Part004

theorem surrogateDiagonalTailChunk000Sub000Block155Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part004] using hcert

def TailChunk000Sub000Block155Part005SupportExplicit : Finset ℕ :=
  ([6437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part005 : ℚ :=
  (2493627709 : ℚ) / 3791099802746880

def SurrogateDiagonalTailChunk000Sub000Block155Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6437
    = surrogateDiagTailX0RatChunk000Sub000Block155Part005

theorem surrogateDiagonalTailChunk000Sub000Block155Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part005] using hcert

def TailChunk000Sub000Block155Part006SupportExplicit : Finset ℕ :=
  ([6438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part006 : ℚ :=
  (273154771325 : ℚ) / 20651850586128384

def SurrogateDiagonalTailChunk000Sub000Block155Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6438
    = surrogateDiagTailX0RatChunk000Sub000Block155Part006

theorem surrogateDiagonalTailChunk000Sub000Block155Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part006] using hcert

def TailChunk000Sub000Block155Part007SupportExplicit : Finset ℕ :=
  ([6439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part007 : ℚ :=
  (834126067125 : ℚ) / 1276710894580105216

def SurrogateDiagonalTailChunk000Sub000Block155Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6439
    = surrogateDiagTailX0RatChunk000Sub000Block155Part007

theorem surrogateDiagonalTailChunk000Sub000Block155Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part007] using hcert

def TailChunk000Sub000Block155Part008SupportExplicit : Finset ℕ :=
  ([6441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part008 : ℚ :=
  (1601409400825 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub000Block155Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6441
    = surrogateDiagTailX0RatChunk000Sub000Block155Part008

theorem surrogateDiagonalTailChunk000Sub000Block155Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part008] using hcert

def TailChunk000Sub000Block155Part009SupportExplicit : Finset ℕ :=
  ([6442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part009 : ℚ :=
  (259371025 : ℚ) / 107525219303712

def SurrogateDiagonalTailChunk000Sub000Block155Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6442
    = surrogateDiagTailX0RatChunk000Sub000Block155Part009

theorem surrogateDiagonalTailChunk000Sub000Block155Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part009] using hcert

def TailChunk000Sub000Block155Part010SupportExplicit : Finset ℕ :=
  ([6443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part010 : ℚ :=
  (2398739253175 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub000Block155Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6443
    = surrogateDiagTailX0RatChunk000Sub000Block155Part010

theorem surrogateDiagonalTailChunk000Sub000Block155Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part010] using hcert

def TailChunk000Sub000Block155Part011SupportExplicit : Finset ℕ :=
  ([6445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part011 : ℚ :=
  (985809710675 : ℚ) / 880846596536008704

def SurrogateDiagonalTailChunk000Sub000Block155Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6445
    = surrogateDiagTailX0RatChunk000Sub000Block155Part011

theorem surrogateDiagonalTailChunk000Sub000Block155Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part011] using hcert

def TailChunk000Sub000Block155Part012SupportExplicit : Finset ℕ :=
  ([6446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part012 : ℚ :=
  (4970960591 : ℚ) / 1454280737187840

def SurrogateDiagonalTailChunk000Sub000Block155Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6446
    = surrogateDiagTailX0RatChunk000Sub000Block155Part012

theorem surrogateDiagonalTailChunk000Sub000Block155Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part012] using hcert

def TailChunk000Sub000Block155Part013SupportExplicit : Finset ℕ :=
  ([6447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part013 : ℚ :=
  (306767995225 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub000Block155Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6447
    = surrogateDiagTailX0RatChunk000Sub000Block155Part013

theorem surrogateDiagonalTailChunk000Sub000Block155Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part013] using hcert

def TailChunk000Sub000Block155Part014SupportExplicit : Finset ℕ :=
  ([6449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part014 : ℚ :=
  (649837515625 : ℚ) / 1080605024979197952

def SurrogateDiagonalTailChunk000Sub000Block155Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6449
    = surrogateDiagTailX0RatChunk000Sub000Block155Part014

theorem surrogateDiagonalTailChunk000Sub000Block155Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part014] using hcert

def TailChunk000Sub000Block155Part015SupportExplicit : Finset ℕ :=
  ([6451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part015 : ℚ :=
  (41615401 : ℚ) / 69244566394050

def SurrogateDiagonalTailChunk000Sub000Block155Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6451
    = surrogateDiagTailX0RatChunk000Sub000Block155Part015

theorem surrogateDiagonalTailChunk000Sub000Block155Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part015] using hcert

def TailChunk000Sub000Block155Part016SupportExplicit : Finset ℕ :=
  ([6454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part016 : ℚ :=
  (4770155473 : ℚ) / 644882614732800

def SurrogateDiagonalTailChunk000Sub000Block155Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6454
    = surrogateDiagTailX0RatChunk000Sub000Block155Part016

theorem surrogateDiagonalTailChunk000Sub000Block155Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part016] using hcert

def TailChunk000Sub000Block155Part017SupportExplicit : Finset ℕ :=
  ([6455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part017 : ℚ :=
  (1648119443 : ℚ) / 1477217416406400

def SurrogateDiagonalTailChunk000Sub000Block155Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6455
    = surrogateDiagTailX0RatChunk000Sub000Block155Part017

theorem surrogateDiagonalTailChunk000Sub000Block155Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part017] using hcert

def TailChunk000Sub000Block155Part018SupportExplicit : Finset ℕ :=
  ([6457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part018 : ℚ :=
  (30953216301 : ℚ) / 39314798992854400

def SurrogateDiagonalTailChunk000Sub000Block155Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6457
    = surrogateDiagTailX0RatChunk000Sub000Block155Part018

theorem surrogateDiagonalTailChunk000Sub000Block155Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part018] using hcert

def TailChunk000Sub000Block155Part019SupportExplicit : Finset ℕ :=
  ([6458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part019 : ℚ :=
  (1303044463975 : ℚ) / 271494454433920128

def SurrogateDiagonalTailChunk000Sub000Block155Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6458
    = surrogateDiagTailX0RatChunk000Sub000Block155Part019

theorem surrogateDiagonalTailChunk000Sub000Block155Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part019] using hcert

def TailChunk000Sub000Block155Part020SupportExplicit : Finset ℕ :=
  ([6459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part020 : ℚ :=
  (724038219425 : ℚ) / 429028273673355264

def SurrogateDiagonalTailChunk000Sub000Block155Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6459
    = surrogateDiagTailX0RatChunk000Sub000Block155Part020

theorem surrogateDiagonalTailChunk000Sub000Block155Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part020] using hcert

def TailChunk000Sub000Block155Part021SupportExplicit : Finset ℕ :=
  ([6461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part021 : ℚ :=
  (77866992169 : ℚ) / 64537033081651200

def SurrogateDiagonalTailChunk000Sub000Block155Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6461
    = surrogateDiagTailX0RatChunk000Sub000Block155Part021

theorem surrogateDiagonalTailChunk000Sub000Block155Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part021] using hcert

def TailChunk000Sub000Block155Part022SupportExplicit : Finset ℕ :=
  ([6463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part022 : ℚ :=
  (98487970243 : ℚ) / 144015653307187200

def SurrogateDiagonalTailChunk000Sub000Block155Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6463
    = surrogateDiagTailX0RatChunk000Sub000Block155Part022

theorem surrogateDiagonalTailChunk000Sub000Block155Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part022] using hcert

def TailChunk000Sub000Block155Part023SupportExplicit : Finset ℕ :=
  ([6465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part023 : ℚ :=
  (7567972779 : ℚ) / 2334368262963200

def SurrogateDiagonalTailChunk000Sub000Block155Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6465
    = surrogateDiagTailX0RatChunk000Sub000Block155Part023

theorem surrogateDiagonalTailChunk000Sub000Block155Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part023] using hcert

def TailChunk000Sub000Block155Part024SupportExplicit : Finset ℕ :=
  ([6466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block155Part024 : ℚ :=
  (50041729099 : ℚ) / 9477749506867200

def SurrogateDiagonalTailChunk000Sub000Block155Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6466
    = surrogateDiagTailX0RatChunk000Sub000Block155Part024

theorem surrogateDiagonalTailChunk000Sub000Block155Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block155Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block155Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block155Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block155Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block155Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block155Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block155HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block155Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block155Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block155Part000
    + surrogateDiagTailX0RatChunk000Sub000Block155Part001
    + surrogateDiagTailX0RatChunk000Sub000Block155Part002
    + surrogateDiagTailX0RatChunk000Sub000Block155Part003
    + surrogateDiagTailX0RatChunk000Sub000Block155Part004
    + surrogateDiagTailX0RatChunk000Sub000Block155Part005
    + surrogateDiagTailX0RatChunk000Sub000Block155Part006
    + surrogateDiagTailX0RatChunk000Sub000Block155Part007
    + surrogateDiagTailX0RatChunk000Sub000Block155Part008
    + surrogateDiagTailX0RatChunk000Sub000Block155Part009

def surrogateDiagonalTailChunk000Sub000Block155MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block155Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block155Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block155Part010
    + surrogateDiagTailX0RatChunk000Sub000Block155Part011
    + surrogateDiagTailX0RatChunk000Sub000Block155Part012
    + surrogateDiagTailX0RatChunk000Sub000Block155Part013
    + surrogateDiagTailX0RatChunk000Sub000Block155Part014
    + surrogateDiagTailX0RatChunk000Sub000Block155Part015
    + surrogateDiagTailX0RatChunk000Sub000Block155Part016
    + surrogateDiagTailX0RatChunk000Sub000Block155Part017
    + surrogateDiagTailX0RatChunk000Sub000Block155Part018
    + surrogateDiagTailX0RatChunk000Sub000Block155Part019

def surrogateDiagonalTailChunk000Sub000Block155TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block155Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block155Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block155Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block155Part020
    + surrogateDiagTailX0RatChunk000Sub000Block155Part021
    + surrogateDiagTailX0RatChunk000Sub000Block155Part022
    + surrogateDiagTailX0RatChunk000Sub000Block155Part023
    + surrogateDiagTailX0RatChunk000Sub000Block155Part024

def surrogateDiagonalTailChunk000Sub000Block155Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block155HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block155MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block155TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block155 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block155Part000
    + surrogateDiagTailX0RatChunk000Sub000Block155Part001
    + surrogateDiagTailX0RatChunk000Sub000Block155Part002
    + surrogateDiagTailX0RatChunk000Sub000Block155Part003
    + surrogateDiagTailX0RatChunk000Sub000Block155Part004
    + surrogateDiagTailX0RatChunk000Sub000Block155Part005
    + surrogateDiagTailX0RatChunk000Sub000Block155Part006
    + surrogateDiagTailX0RatChunk000Sub000Block155Part007
    + surrogateDiagTailX0RatChunk000Sub000Block155Part008
    + surrogateDiagTailX0RatChunk000Sub000Block155Part009
    + surrogateDiagTailX0RatChunk000Sub000Block155Part010
    + surrogateDiagTailX0RatChunk000Sub000Block155Part011
    + surrogateDiagTailX0RatChunk000Sub000Block155Part012
    + surrogateDiagTailX0RatChunk000Sub000Block155Part013
    + surrogateDiagTailX0RatChunk000Sub000Block155Part014
    + surrogateDiagTailX0RatChunk000Sub000Block155Part015
    + surrogateDiagTailX0RatChunk000Sub000Block155Part016
    + surrogateDiagTailX0RatChunk000Sub000Block155Part017
    + surrogateDiagTailX0RatChunk000Sub000Block155Part018
    + surrogateDiagTailX0RatChunk000Sub000Block155Part019
    + surrogateDiagTailX0RatChunk000Sub000Block155Part020
    + surrogateDiagTailX0RatChunk000Sub000Block155Part021
    + surrogateDiagTailX0RatChunk000Sub000Block155Part022
    + surrogateDiagTailX0RatChunk000Sub000Block155Part023
    + surrogateDiagTailX0RatChunk000Sub000Block155Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block155_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block155Head + surrogateDiagTailX0RatChunk000Sub000Block155Mid + surrogateDiagTailX0RatChunk000Sub000Block155Tail =
      surrogateDiagTailX0RatChunk000Sub000Block155 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block155Head surrogateDiagTailX0RatChunk000Sub000Block155Mid surrogateDiagTailX0RatChunk000Sub000Block155Tail surrogateDiagTailX0RatChunk000Sub000Block155
  ring

def SurrogateDiagonalTailChunk000Sub000Block155HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block155HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block155Head

def SurrogateDiagonalTailChunk000Sub000Block155MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block155MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block155Mid

def SurrogateDiagonalTailChunk000Sub000Block155TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block155TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block155Tail

theorem surrogateDiagonalTailChunk000Sub000Block155_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block155HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block155MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block155TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block155Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block155 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block155HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block155MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block155TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block155Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block155_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
