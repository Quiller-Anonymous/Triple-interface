import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [120,130). -/

/-- Block 120 covers tail-support indices [13000,13025) and q from 21431 to 21471. -/

def TailChunk001Sub000Block120Part000SupportExplicit : Finset ℕ :=
  ([21431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part000 : ℚ :=
  (82242569075 : ℚ) / 151971859281533147136

def SurrogateDiagonalTailChunk001Sub000Block120Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21431
    = surrogateDiagTailX0RatChunk001Sub000Block120Part000

theorem surrogateDiagonalTailChunk001Sub000Block120Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part000] using hcert

def TailChunk001Sub000Block120Part001SupportExplicit : Finset ℕ :=
  ([21433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block120Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21433
    = surrogateDiagTailX0RatChunk001Sub000Block120Part001

theorem surrogateDiagonalTailChunk001Sub000Block120Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part001] using hcert

def TailChunk001Sub000Block120Part002SupportExplicit : Finset ℕ :=
  ([21434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part002 : ℚ :=
  (3476345383 : ℚ) / 11098840264438050

def SurrogateDiagonalTailChunk001Sub000Block120Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21434
    = surrogateDiagTailX0RatChunk001Sub000Block120Part002

theorem surrogateDiagonalTailChunk001Sub000Block120Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part002] using hcert

def TailChunk001Sub000Block120Part003SupportExplicit : Finset ℕ :=
  ([21435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part003 : ℚ :=
  (233877587075 : ℚ) / 3549101260913639424

def SurrogateDiagonalTailChunk001Sub000Block120Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21435
    = surrogateDiagTailX0RatChunk001Sub000Block120Part003

theorem surrogateDiagonalTailChunk001Sub000Block120Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part003] using hcert

def TailChunk001Sub000Block120Part004SupportExplicit : Finset ℕ :=
  ([21437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part004 : ℚ :=
  (143448484525 : ℚ) / 48102257126642024448

def SurrogateDiagonalTailChunk001Sub000Block120Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21437
    = surrogateDiagTailX0RatChunk001Sub000Block120Part004

theorem surrogateDiagonalTailChunk001Sub000Block120Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part004] using hcert

def TailChunk001Sub000Block120Part005SupportExplicit : Finset ℕ :=
  ([21439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part005 : ℚ :=
  (28573987477 : ℚ) / 14402658403305523200

def SurrogateDiagonalTailChunk001Sub000Block120Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21439
    = surrogateDiagTailX0RatChunk001Sub000Block120Part005

theorem surrogateDiagonalTailChunk001Sub000Block120Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part005] using hcert

def TailChunk001Sub000Block120Part006SupportExplicit : Finset ℕ :=
  ([21441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part006 : ℚ :=
  (6588365621 : ℚ) / 132057660778905600

def SurrogateDiagonalTailChunk001Sub000Block120Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21441
    = surrogateDiagTailX0RatChunk001Sub000Block120Part006

theorem surrogateDiagonalTailChunk001Sub000Block120Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part006] using hcert

def TailChunk001Sub000Block120Part007SupportExplicit : Finset ℕ :=
  ([21442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part007 : ℚ :=
  (10308204197 : ℚ) / 45027753750000000

def SurrogateDiagonalTailChunk001Sub000Block120Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21442
    = surrogateDiagTailX0RatChunk001Sub000Block120Part007

theorem surrogateDiagonalTailChunk001Sub000Block120Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part007] using hcert

def TailChunk001Sub000Block120Part008SupportExplicit : Finset ℕ :=
  ([21443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part008 : ℚ :=
  (6621308581 : ℚ) / 19011169219085107200

def SurrogateDiagonalTailChunk001Sub000Block120Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21443
    = surrogateDiagTailX0RatChunk001Sub000Block120Part008

theorem surrogateDiagonalTailChunk001Sub000Block120Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part008] using hcert

def TailChunk001Sub000Block120Part009SupportExplicit : Finset ℕ :=
  ([21445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part009 : ℚ :=
  (383478217125 : ℚ) / 72138096128227803136

def SurrogateDiagonalTailChunk001Sub000Block120Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21445
    = surrogateDiagTailX0RatChunk001Sub000Block120Part009

theorem surrogateDiagonalTailChunk001Sub000Block120Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part009] using hcert

def TailChunk001Sub000Block120Part010SupportExplicit : Finset ℕ :=
  ([21446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part010 : ℚ :=
  (1796605140625 : ℚ) / 8261712523932776082

def SurrogateDiagonalTailChunk001Sub000Block120Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21446
    = surrogateDiagTailX0RatChunk001Sub000Block120Part010

theorem surrogateDiagonalTailChunk001Sub000Block120Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part010] using hcert

def TailChunk001Sub000Block120Part011SupportExplicit : Finset ℕ :=
  ([21449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part011 : ℚ :=
  (458609069 : ℚ) / 2211159118499020800

def SurrogateDiagonalTailChunk001Sub000Block120Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21449
    = surrogateDiagTailX0RatChunk001Sub000Block120Part011

theorem surrogateDiagonalTailChunk001Sub000Block120Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part011] using hcert

def TailChunk001Sub000Block120Part012SupportExplicit : Finset ℕ :=
  ([21451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part012 : ℚ :=
  (50365556225 : ℚ) / 53120639033980194816

def SurrogateDiagonalTailChunk001Sub000Block120Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21451
    = surrogateDiagTailX0RatChunk001Sub000Block120Part012

theorem surrogateDiagonalTailChunk001Sub000Block120Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part012] using hcert

def TailChunk001Sub000Block120Part013SupportExplicit : Finset ℕ :=
  ([21453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part013 : ℚ :=
  (2556625007 : ℚ) / 83649046664040000

def SurrogateDiagonalTailChunk001Sub000Block120Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21453
    = surrogateDiagTailX0RatChunk001Sub000Block120Part013

theorem surrogateDiagonalTailChunk001Sub000Block120Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part013] using hcert

def TailChunk001Sub000Block120Part014SupportExplicit : Finset ℕ :=
  ([21454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part014 : ℚ :=
  (888425543 : ℚ) / 3512219487436800

def SurrogateDiagonalTailChunk001Sub000Block120Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21454
    = surrogateDiagTailX0RatChunk001Sub000Block120Part014

theorem surrogateDiagonalTailChunk001Sub000Block120Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part014] using hcert

def TailChunk001Sub000Block120Part015SupportExplicit : Finset ℕ :=
  ([21455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part015 : ℚ :=
  (1365421144375 : ℚ) / 116379775291233927168

def SurrogateDiagonalTailChunk001Sub000Block120Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21455
    = surrogateDiagTailX0RatChunk001Sub000Block120Part015

theorem surrogateDiagonalTailChunk001Sub000Block120Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part015] using hcert

def TailChunk001Sub000Block120Part016SupportExplicit : Finset ℕ :=
  ([21457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part016 : ℚ :=
  (23989287325 : ℚ) / 68366500722692452224

def SurrogateDiagonalTailChunk001Sub000Block120Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21457
    = surrogateDiagTailX0RatChunk001Sub000Block120Part016

theorem surrogateDiagonalTailChunk001Sub000Block120Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part016] using hcert

def TailChunk001Sub000Block120Part017SupportExplicit : Finset ℕ :=
  ([21458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part017 : ℚ :=
  (1798616265625 : ℚ) / 8280220973752300032

def SurrogateDiagonalTailChunk001Sub000Block120Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21458
    = surrogateDiagTailX0RatChunk001Sub000Block120Part017

theorem surrogateDiagonalTailChunk001Sub000Block120Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part017] using hcert

def TailChunk001Sub000Block120Part018SupportExplicit : Finset ℕ :=
  ([21459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part018 : ℚ :=
  (4158357147 : ℚ) / 115404588502973440

def SurrogateDiagonalTailChunk001Sub000Block120Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21459
    = surrogateDiagTailX0RatChunk001Sub000Block120Part018

theorem surrogateDiagonalTailChunk001Sub000Block120Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part018] using hcert

def TailChunk001Sub000Block120Part019SupportExplicit : Finset ℕ :=
  ([21461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part019 : ℚ :=
  (398621023 : ℚ) / 301289542734375000

def SurrogateDiagonalTailChunk001Sub000Block120Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21461
    = surrogateDiagTailX0RatChunk001Sub000Block120Part019

theorem surrogateDiagonalTailChunk001Sub000Block120Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part019] using hcert

def TailChunk001Sub000Block120Part020SupportExplicit : Finset ℕ :=
  ([21466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part020 : ℚ :=
  (1799957640625 : ℚ) / 8292577205103619872

def SurrogateDiagonalTailChunk001Sub000Block120Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21466
    = surrogateDiagTailX0RatChunk001Sub000Block120Part020

theorem surrogateDiagonalTailChunk001Sub000Block120Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part020] using hcert

def TailChunk001Sub000Block120Part021SupportExplicit : Finset ℕ :=
  ([21467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block120Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21467
    = surrogateDiagTailX0RatChunk001Sub000Block120Part021

theorem surrogateDiagonalTailChunk001Sub000Block120Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part021] using hcert

def TailChunk001Sub000Block120Part022SupportExplicit : Finset ℕ :=
  ([21469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part022 : ℚ :=
  (589397153125 : ℚ) / 286365346699641164928

def SurrogateDiagonalTailChunk001Sub000Block120Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21469
    = surrogateDiagTailX0RatChunk001Sub000Block120Part022

theorem surrogateDiagonalTailChunk001Sub000Block120Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part022] using hcert

def TailChunk001Sub000Block120Part023SupportExplicit : Finset ℕ :=
  ([21470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part023 : ℚ :=
  (4721935107775 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk001Sub000Block120Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21470
    = surrogateDiagTailX0RatChunk001Sub000Block120Part023

theorem surrogateDiagonalTailChunk001Sub000Block120Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part023] using hcert

def TailChunk001Sub000Block120Part024SupportExplicit : Finset ℕ :=
  ([21471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block120Part024 : ℚ :=
  (123437233807 : ℚ) / 3263502314844979200

def SurrogateDiagonalTailChunk001Sub000Block120Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21471
    = surrogateDiagTailX0RatChunk001Sub000Block120Part024

theorem surrogateDiagonalTailChunk001Sub000Block120Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block120Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block120Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block120Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block120Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block120Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block120HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block120Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block120Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block120Part000
    + surrogateDiagTailX0RatChunk001Sub000Block120Part001
    + surrogateDiagTailX0RatChunk001Sub000Block120Part002
    + surrogateDiagTailX0RatChunk001Sub000Block120Part003
    + surrogateDiagTailX0RatChunk001Sub000Block120Part004
    + surrogateDiagTailX0RatChunk001Sub000Block120Part005
    + surrogateDiagTailX0RatChunk001Sub000Block120Part006
    + surrogateDiagTailX0RatChunk001Sub000Block120Part007
    + surrogateDiagTailX0RatChunk001Sub000Block120Part008
    + surrogateDiagTailX0RatChunk001Sub000Block120Part009

def surrogateDiagonalTailChunk001Sub000Block120MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block120Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block120Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block120Part010
    + surrogateDiagTailX0RatChunk001Sub000Block120Part011
    + surrogateDiagTailX0RatChunk001Sub000Block120Part012
    + surrogateDiagTailX0RatChunk001Sub000Block120Part013
    + surrogateDiagTailX0RatChunk001Sub000Block120Part014
    + surrogateDiagTailX0RatChunk001Sub000Block120Part015
    + surrogateDiagTailX0RatChunk001Sub000Block120Part016
    + surrogateDiagTailX0RatChunk001Sub000Block120Part017
    + surrogateDiagTailX0RatChunk001Sub000Block120Part018
    + surrogateDiagTailX0RatChunk001Sub000Block120Part019

def surrogateDiagonalTailChunk001Sub000Block120TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block120Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block120Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block120Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block120Part020
    + surrogateDiagTailX0RatChunk001Sub000Block120Part021
    + surrogateDiagTailX0RatChunk001Sub000Block120Part022
    + surrogateDiagTailX0RatChunk001Sub000Block120Part023
    + surrogateDiagTailX0RatChunk001Sub000Block120Part024

def surrogateDiagonalTailChunk001Sub000Block120Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block120HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block120MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block120TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block120 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block120Part000
    + surrogateDiagTailX0RatChunk001Sub000Block120Part001
    + surrogateDiagTailX0RatChunk001Sub000Block120Part002
    + surrogateDiagTailX0RatChunk001Sub000Block120Part003
    + surrogateDiagTailX0RatChunk001Sub000Block120Part004
    + surrogateDiagTailX0RatChunk001Sub000Block120Part005
    + surrogateDiagTailX0RatChunk001Sub000Block120Part006
    + surrogateDiagTailX0RatChunk001Sub000Block120Part007
    + surrogateDiagTailX0RatChunk001Sub000Block120Part008
    + surrogateDiagTailX0RatChunk001Sub000Block120Part009
    + surrogateDiagTailX0RatChunk001Sub000Block120Part010
    + surrogateDiagTailX0RatChunk001Sub000Block120Part011
    + surrogateDiagTailX0RatChunk001Sub000Block120Part012
    + surrogateDiagTailX0RatChunk001Sub000Block120Part013
    + surrogateDiagTailX0RatChunk001Sub000Block120Part014
    + surrogateDiagTailX0RatChunk001Sub000Block120Part015
    + surrogateDiagTailX0RatChunk001Sub000Block120Part016
    + surrogateDiagTailX0RatChunk001Sub000Block120Part017
    + surrogateDiagTailX0RatChunk001Sub000Block120Part018
    + surrogateDiagTailX0RatChunk001Sub000Block120Part019
    + surrogateDiagTailX0RatChunk001Sub000Block120Part020
    + surrogateDiagTailX0RatChunk001Sub000Block120Part021
    + surrogateDiagTailX0RatChunk001Sub000Block120Part022
    + surrogateDiagTailX0RatChunk001Sub000Block120Part023
    + surrogateDiagTailX0RatChunk001Sub000Block120Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block120_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block120Head + surrogateDiagTailX0RatChunk001Sub000Block120Mid + surrogateDiagTailX0RatChunk001Sub000Block120Tail =
      surrogateDiagTailX0RatChunk001Sub000Block120 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block120Head surrogateDiagTailX0RatChunk001Sub000Block120Mid surrogateDiagTailX0RatChunk001Sub000Block120Tail surrogateDiagTailX0RatChunk001Sub000Block120
  ring

def SurrogateDiagonalTailChunk001Sub000Block120HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block120HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block120Head

def SurrogateDiagonalTailChunk001Sub000Block120MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block120MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block120Mid

def SurrogateDiagonalTailChunk001Sub000Block120TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block120TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block120Tail

theorem surrogateDiagonalTailChunk001Sub000Block120_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block120HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block120MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block120TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block120Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block120 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block120HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block120MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block120TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block120Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block120_eq_head_add_mid_add_tail

/-- Block 121 covers tail-support indices [13025,13050) and q from 21473 to 21513. -/

def TailChunk001Sub000Block121Part000SupportExplicit : Finset ℕ :=
  ([21473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part000 : ℚ :=
  (636606125 : ℚ) / 3415299790680981504

def SurrogateDiagonalTailChunk001Sub000Block121Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21473
    = surrogateDiagTailX0RatChunk001Sub000Block121Part000

theorem surrogateDiagonalTailChunk001Sub000Block121Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part000] using hcert

def TailChunk001Sub000Block121Part001SupportExplicit : Finset ℕ :=
  ([21477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part001 : ℚ :=
  (1601467629275 : ℚ) / 52515030504665669184

def SurrogateDiagonalTailChunk001Sub000Block121Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21477
    = surrogateDiagTailX0RatChunk001Sub000Block121Part001

theorem surrogateDiagonalTailChunk001Sub000Block121Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part001] using hcert

def TailChunk001Sub000Block121Part002SupportExplicit : Finset ℕ :=
  ([21478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part002 : ℚ :=
  (1801970640625 : ℚ) / 8311137475095205842

def SurrogateDiagonalTailChunk001Sub000Block121Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21478
    = surrogateDiagTailX0RatChunk001Sub000Block121Part002

theorem surrogateDiagonalTailChunk001Sub000Block121Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part002] using hcert

def TailChunk001Sub000Block121Part003SupportExplicit : Finset ℕ :=
  ([21479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part003 : ℚ :=
  (78498852575 : ℚ) / 242040232035628498944

def SurrogateDiagonalTailChunk001Sub000Block121Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21479
    = surrogateDiagTailX0RatChunk001Sub000Block121Part003

theorem surrogateDiagonalTailChunk001Sub000Block121Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part003] using hcert

def TailChunk001Sub000Block121Part004SupportExplicit : Finset ℕ :=
  ([21481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21481
    = surrogateDiagTailX0RatChunk001Sub000Block121Part004

theorem surrogateDiagonalTailChunk001Sub000Block121Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part004] using hcert

def TailChunk001Sub000Block121Part005SupportExplicit : Finset ℕ :=
  ([21482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part005 : ℚ :=
  (6712472217325 : ℚ) / 27622389755971579008

def SurrogateDiagonalTailChunk001Sub000Block121Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21482
    = surrogateDiagTailX0RatChunk001Sub000Block121Part005

theorem surrogateDiagonalTailChunk001Sub000Block121Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part005] using hcert

def TailChunk001Sub000Block121Part006SupportExplicit : Finset ℕ :=
  ([21485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part006 : ℚ :=
  (1154726650375 : ℚ) / 218033845690780090368

def SurrogateDiagonalTailChunk001Sub000Block121Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21485
    = surrogateDiagTailX0RatChunk001Sub000Block121Part006

theorem surrogateDiagonalTailChunk001Sub000Block121Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part006] using hcert

def TailChunk001Sub000Block121Part007SupportExplicit : Finset ℕ :=
  ([21486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part007 : ℚ :=
  (80127813359 : ℚ) / 131434368785433600

def SurrogateDiagonalTailChunk001Sub000Block121Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21486
    = surrogateDiagTailX0RatChunk001Sub000Block121Part007

theorem surrogateDiagonalTailChunk001Sub000Block121Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part007] using hcert

def TailChunk001Sub000Block121Part008SupportExplicit : Finset ℕ :=
  ([21487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21487
    = surrogateDiagTailX0RatChunk001Sub000Block121Part008

theorem surrogateDiagonalTailChunk001Sub000Block121Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part008] using hcert

def TailChunk001Sub000Block121Part009SupportExplicit : Finset ℕ :=
  ([21489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part009 : ℚ :=
  (957694137275 : ℚ) / 17843198906414923776

def SurrogateDiagonalTailChunk001Sub000Block121Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21489
    = surrogateDiagTailX0RatChunk001Sub000Block121Part009

theorem surrogateDiagonalTailChunk001Sub000Block121Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part009] using hcert

def TailChunk001Sub000Block121Part010SupportExplicit : Finset ℕ :=
  ([21490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part010 : ℚ :=
  (774097052875 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk001Sub000Block121Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21490
    = surrogateDiagTailX0RatChunk001Sub000Block121Part010

theorem surrogateDiagonalTailChunk001Sub000Block121Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part010] using hcert

def TailChunk001Sub000Block121Part011SupportExplicit : Finset ℕ :=
  ([21491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21491
    = surrogateDiagTailX0RatChunk001Sub000Block121Part011

theorem surrogateDiagonalTailChunk001Sub000Block121Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part011] using hcert

def TailChunk001Sub000Block121Part012SupportExplicit : Finset ℕ :=
  ([21493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21493
    = surrogateDiagTailX0RatChunk001Sub000Block121Part012

theorem surrogateDiagonalTailChunk001Sub000Block121Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part012] using hcert

def TailChunk001Sub000Block121Part013SupportExplicit : Finset ℕ :=
  ([21494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part013 : ℚ :=
  (60113789 : ℚ) / 4537912579915776

def SurrogateDiagonalTailChunk001Sub000Block121Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21494
    = surrogateDiagTailX0RatChunk001Sub000Block121Part013

theorem surrogateDiagonalTailChunk001Sub000Block121Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part013] using hcert

def TailChunk001Sub000Block121Part014SupportExplicit : Finset ℕ :=
  ([21495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part014 : ℚ :=
  (705565476325 : ℚ) / 10767103490902720512

def SurrogateDiagonalTailChunk001Sub000Block121Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21495
    = surrogateDiagTailX0RatChunk001Sub000Block121Part014

theorem surrogateDiagonalTailChunk001Sub000Block121Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part014] using hcert

def TailChunk001Sub000Block121Part015SupportExplicit : Finset ℕ :=
  ([21497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part015 : ℚ :=
  (1312243591075 : ℚ) / 246091873755352301568

def SurrogateDiagonalTailChunk001Sub000Block121Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21497
    = surrogateDiagTailX0RatChunk001Sub000Block121Part015

theorem surrogateDiagonalTailChunk001Sub000Block121Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part015] using hcert

def TailChunk001Sub000Block121Part016SupportExplicit : Finset ℕ :=
  ([21498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part016 : ℚ :=
  (401272673975 : ℚ) / 3293208077196976704

def SurrogateDiagonalTailChunk001Sub000Block121Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21498
    = surrogateDiagTailX0RatChunk001Sub000Block121Part016

theorem surrogateDiagonalTailChunk001Sub000Block121Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part016] using hcert

def TailChunk001Sub000Block121Part017SupportExplicit : Finset ℕ :=
  ([21499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21499
    = surrogateDiagTailX0RatChunk001Sub000Block121Part017

theorem surrogateDiagonalTailChunk001Sub000Block121Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part017] using hcert

def TailChunk001Sub000Block121Part018SupportExplicit : Finset ℕ :=
  ([21502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part018 : ℚ :=
  (259350281875 : ℚ) / 24136374312324384768

def SurrogateDiagonalTailChunk001Sub000Block121Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21502
    = surrogateDiagTailX0RatChunk001Sub000Block121Part018

theorem surrogateDiagonalTailChunk001Sub000Block121Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part018] using hcert

def TailChunk001Sub000Block121Part019SupportExplicit : Finset ℕ :=
  ([21503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21503
    = surrogateDiagTailX0RatChunk001Sub000Block121Part019

theorem surrogateDiagonalTailChunk001Sub000Block121Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part019] using hcert

def TailChunk001Sub000Block121Part020SupportExplicit : Finset ℕ :=
  ([21505] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part020 : ℚ :=
  (22532985753 : ℚ) / 1310316514666086400

def SurrogateDiagonalTailChunk001Sub000Block121Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21505
    = surrogateDiagTailX0RatChunk001Sub000Block121Part020

theorem surrogateDiagonalTailChunk001Sub000Block121Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part020] using hcert

def TailChunk001Sub000Block121Part021SupportExplicit : Finset ℕ :=
  ([21506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block121Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21506
    = surrogateDiagTailX0RatChunk001Sub000Block121Part021

theorem surrogateDiagonalTailChunk001Sub000Block121Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part021] using hcert

def TailChunk001Sub000Block121Part022SupportExplicit : Finset ℕ :=
  ([21507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part022 : ℚ :=
  (3166159110325 : ℚ) / 95839832221947906048

def SurrogateDiagonalTailChunk001Sub000Block121Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21507
    = surrogateDiagTailX0RatChunk001Sub000Block121Part022

theorem surrogateDiagonalTailChunk001Sub000Block121Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part022] using hcert

def TailChunk001Sub000Block121Part023SupportExplicit : Finset ℕ :=
  ([21509] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part023 : ℚ :=
  (45723247325 : ℚ) / 253309157300177731584

def SurrogateDiagonalTailChunk001Sub000Block121Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21509
    = surrogateDiagTailX0RatChunk001Sub000Block121Part023

theorem surrogateDiagonalTailChunk001Sub000Block121Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part023] using hcert

def TailChunk001Sub000Block121Part024SupportExplicit : Finset ℕ :=
  ([21513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block121Part024 : ℚ :=
  (126641451781 : ℚ) / 3842368320000000000

def SurrogateDiagonalTailChunk001Sub000Block121Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21513
    = surrogateDiagTailX0RatChunk001Sub000Block121Part024

theorem surrogateDiagonalTailChunk001Sub000Block121Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block121Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block121Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block121Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block121Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block121Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block121HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block121Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block121Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block121Part000
    + surrogateDiagTailX0RatChunk001Sub000Block121Part001
    + surrogateDiagTailX0RatChunk001Sub000Block121Part002
    + surrogateDiagTailX0RatChunk001Sub000Block121Part003
    + surrogateDiagTailX0RatChunk001Sub000Block121Part004
    + surrogateDiagTailX0RatChunk001Sub000Block121Part005
    + surrogateDiagTailX0RatChunk001Sub000Block121Part006
    + surrogateDiagTailX0RatChunk001Sub000Block121Part007
    + surrogateDiagTailX0RatChunk001Sub000Block121Part008
    + surrogateDiagTailX0RatChunk001Sub000Block121Part009

def surrogateDiagonalTailChunk001Sub000Block121MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block121Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block121Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block121Part010
    + surrogateDiagTailX0RatChunk001Sub000Block121Part011
    + surrogateDiagTailX0RatChunk001Sub000Block121Part012
    + surrogateDiagTailX0RatChunk001Sub000Block121Part013
    + surrogateDiagTailX0RatChunk001Sub000Block121Part014
    + surrogateDiagTailX0RatChunk001Sub000Block121Part015
    + surrogateDiagTailX0RatChunk001Sub000Block121Part016
    + surrogateDiagTailX0RatChunk001Sub000Block121Part017
    + surrogateDiagTailX0RatChunk001Sub000Block121Part018
    + surrogateDiagTailX0RatChunk001Sub000Block121Part019

def surrogateDiagonalTailChunk001Sub000Block121TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block121Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block121Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block121Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block121Part020
    + surrogateDiagTailX0RatChunk001Sub000Block121Part021
    + surrogateDiagTailX0RatChunk001Sub000Block121Part022
    + surrogateDiagTailX0RatChunk001Sub000Block121Part023
    + surrogateDiagTailX0RatChunk001Sub000Block121Part024

def surrogateDiagonalTailChunk001Sub000Block121Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block121HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block121MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block121TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block121 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block121Part000
    + surrogateDiagTailX0RatChunk001Sub000Block121Part001
    + surrogateDiagTailX0RatChunk001Sub000Block121Part002
    + surrogateDiagTailX0RatChunk001Sub000Block121Part003
    + surrogateDiagTailX0RatChunk001Sub000Block121Part004
    + surrogateDiagTailX0RatChunk001Sub000Block121Part005
    + surrogateDiagTailX0RatChunk001Sub000Block121Part006
    + surrogateDiagTailX0RatChunk001Sub000Block121Part007
    + surrogateDiagTailX0RatChunk001Sub000Block121Part008
    + surrogateDiagTailX0RatChunk001Sub000Block121Part009
    + surrogateDiagTailX0RatChunk001Sub000Block121Part010
    + surrogateDiagTailX0RatChunk001Sub000Block121Part011
    + surrogateDiagTailX0RatChunk001Sub000Block121Part012
    + surrogateDiagTailX0RatChunk001Sub000Block121Part013
    + surrogateDiagTailX0RatChunk001Sub000Block121Part014
    + surrogateDiagTailX0RatChunk001Sub000Block121Part015
    + surrogateDiagTailX0RatChunk001Sub000Block121Part016
    + surrogateDiagTailX0RatChunk001Sub000Block121Part017
    + surrogateDiagTailX0RatChunk001Sub000Block121Part018
    + surrogateDiagTailX0RatChunk001Sub000Block121Part019
    + surrogateDiagTailX0RatChunk001Sub000Block121Part020
    + surrogateDiagTailX0RatChunk001Sub000Block121Part021
    + surrogateDiagTailX0RatChunk001Sub000Block121Part022
    + surrogateDiagTailX0RatChunk001Sub000Block121Part023
    + surrogateDiagTailX0RatChunk001Sub000Block121Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block121_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block121Head + surrogateDiagTailX0RatChunk001Sub000Block121Mid + surrogateDiagTailX0RatChunk001Sub000Block121Tail =
      surrogateDiagTailX0RatChunk001Sub000Block121 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block121Head surrogateDiagTailX0RatChunk001Sub000Block121Mid surrogateDiagTailX0RatChunk001Sub000Block121Tail surrogateDiagTailX0RatChunk001Sub000Block121
  ring

def SurrogateDiagonalTailChunk001Sub000Block121HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block121HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block121Head

def SurrogateDiagonalTailChunk001Sub000Block121MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block121MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block121Mid

def SurrogateDiagonalTailChunk001Sub000Block121TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block121TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block121Tail

theorem surrogateDiagonalTailChunk001Sub000Block121_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block121HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block121MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block121TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block121Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block121 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block121HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block121MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block121TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block121Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block121_eq_head_add_mid_add_tail

/-- Block 122 covers tail-support indices [13050,13075) and q from 21514 to 21554. -/

def TailChunk001Sub000Block122Part000SupportExplicit : Finset ℕ :=
  ([21514] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part000 : ℚ :=
  (242557061 : ℚ) / 58055887512531360

def SurrogateDiagonalTailChunk001Sub000Block122Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21514
    = surrogateDiagTailX0RatChunk001Sub000Block122Part000

theorem surrogateDiagonalTailChunk001Sub000Block122Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part000] using hcert

def TailChunk001Sub000Block122Part001SupportExplicit : Finset ℕ :=
  ([21515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part001 : ℚ :=
  (3103820287 : ℚ) / 349812282418790400

def SurrogateDiagonalTailChunk001Sub000Block122Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21515
    = surrogateDiagTailX0RatChunk001Sub000Block122Part001

theorem surrogateDiagonalTailChunk001Sub000Block122Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part001] using hcert

def TailChunk001Sub000Block122Part002SupportExplicit : Finset ℕ :=
  ([21517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block122Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21517
    = surrogateDiagTailX0RatChunk001Sub000Block122Part002

theorem surrogateDiagonalTailChunk001Sub000Block122Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part002] using hcert

def TailChunk001Sub000Block122Part003SupportExplicit : Finset ℕ :=
  ([21518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part003 : ℚ :=
  (273450064625 : ℚ) / 7281944501116207104

def SurrogateDiagonalTailChunk001Sub000Block122Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21518
    = surrogateDiagTailX0RatChunk001Sub000Block122Part003

theorem surrogateDiagonalTailChunk001Sub000Block122Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part003] using hcert

def TailChunk001Sub000Block122Part004SupportExplicit : Finset ℕ :=
  ([21521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block122Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21521
    = surrogateDiagTailX0RatChunk001Sub000Block122Part004

theorem surrogateDiagonalTailChunk001Sub000Block122Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part004] using hcert

def TailChunk001Sub000Block122Part005SupportExplicit : Finset ℕ :=
  ([21522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part005 : ℚ :=
  (6761035037 : ℚ) / 40793778935562240

def SurrogateDiagonalTailChunk001Sub000Block122Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21522
    = surrogateDiagTailX0RatChunk001Sub000Block122Part005

theorem surrogateDiagonalTailChunk001Sub000Block122Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part005] using hcert

def TailChunk001Sub000Block122Part006SupportExplicit : Finset ℕ :=
  ([21523] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block122Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21523
    = surrogateDiagTailX0RatChunk001Sub000Block122Part006

theorem surrogateDiagonalTailChunk001Sub000Block122Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part006] using hcert

def TailChunk001Sub000Block122Part007SupportExplicit : Finset ℕ :=
  ([21526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part007 : ℚ :=
  (890659825 : ℚ) / 315156552129724608

def SurrogateDiagonalTailChunk001Sub000Block122Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21526
    = surrogateDiagTailX0RatChunk001Sub000Block122Part007

theorem surrogateDiagonalTailChunk001Sub000Block122Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part007] using hcert

def TailChunk001Sub000Block122Part008SupportExplicit : Finset ℕ :=
  ([21527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part008 : ℚ :=
  (38997523603 : ℚ) / 11365212430784563200

def SurrogateDiagonalTailChunk001Sub000Block122Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21527
    = surrogateDiagTailX0RatChunk001Sub000Block122Part008

theorem surrogateDiagonalTailChunk001Sub000Block122Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part008] using hcert

def TailChunk001Sub000Block122Part009SupportExplicit : Finset ℕ :=
  ([21529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block122Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21529
    = surrogateDiagTailX0RatChunk001Sub000Block122Part009

theorem surrogateDiagonalTailChunk001Sub000Block122Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part009] using hcert

def TailChunk001Sub000Block122Part010SupportExplicit : Finset ℕ :=
  ([21530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part010 : ℚ :=
  (580022701525 : ℚ) / 13728904757547368448

def SurrogateDiagonalTailChunk001Sub000Block122Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21530
    = surrogateDiagTailX0RatChunk001Sub000Block122Part010

theorem surrogateDiagonalTailChunk001Sub000Block122Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part010] using hcert

def TailChunk001Sub000Block122Part011SupportExplicit : Finset ℕ :=
  ([21531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part011 : ℚ :=
  (804765252025 : ℚ) / 26522628997512241152

def SurrogateDiagonalTailChunk001Sub000Block122Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21531
    = surrogateDiagTailX0RatChunk001Sub000Block122Part011

theorem surrogateDiagonalTailChunk001Sub000Block122Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part011] using hcert

def TailChunk001Sub000Block122Part012SupportExplicit : Finset ℕ :=
  ([21533] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part012 : ℚ :=
  (634462907 : ℚ) / 2487554008311398400

def SurrogateDiagonalTailChunk001Sub000Block122Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21533
    = surrogateDiagTailX0RatChunk001Sub000Block122Part012

theorem surrogateDiagonalTailChunk001Sub000Block122Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part012] using hcert

def TailChunk001Sub000Block122Part013SupportExplicit : Finset ℕ :=
  ([21534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part013 : ℚ :=
  (30653776925 : ℚ) / 211386872138563584

def SurrogateDiagonalTailChunk001Sub000Block122Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21534
    = surrogateDiagTailX0RatChunk001Sub000Block122Part013

theorem surrogateDiagonalTailChunk001Sub000Block122Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part013] using hcert

def TailChunk001Sub000Block122Part014SupportExplicit : Finset ℕ :=
  ([21535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part014 : ℚ :=
  (417391400575 : ℚ) / 64891457601143832576

def SurrogateDiagonalTailChunk001Sub000Block122Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21535
    = surrogateDiagTailX0RatChunk001Sub000Block122Part014

theorem surrogateDiagonalTailChunk001Sub000Block122Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part014] using hcert

def TailChunk001Sub000Block122Part015SupportExplicit : Finset ℕ :=
  ([21539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part015 : ℚ :=
  (28054050671 : ℚ) / 4458941834172825600

def SurrogateDiagonalTailChunk001Sub000Block122Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21539
    = surrogateDiagTailX0RatChunk001Sub000Block122Part015

theorem surrogateDiagonalTailChunk001Sub000Block122Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part015] using hcert

def TailChunk001Sub000Block122Part016SupportExplicit : Finset ℕ :=
  ([21541] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part016 : ℚ :=
  (258867758975 : ℚ) / 194967928408868388864

def SurrogateDiagonalTailChunk001Sub000Block122Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21541
    = surrogateDiagTailX0RatChunk001Sub000Block122Part016

theorem surrogateDiagonalTailChunk001Sub000Block122Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part016] using hcert

def TailChunk001Sub000Block122Part017SupportExplicit : Finset ℕ :=
  ([21542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block122Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21542
    = surrogateDiagTailX0RatChunk001Sub000Block122Part017

theorem surrogateDiagonalTailChunk001Sub000Block122Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part017] using hcert

def TailChunk001Sub000Block122Part018SupportExplicit : Finset ℕ :=
  ([21543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part018 : ℚ :=
  (789778464625 : ℚ) / 23632864447350477312

def SurrogateDiagonalTailChunk001Sub000Block122Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21543
    = surrogateDiagTailX0RatChunk001Sub000Block122Part018

theorem surrogateDiagonalTailChunk001Sub000Block122Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part018] using hcert

def TailChunk001Sub000Block122Part019SupportExplicit : Finset ℕ :=
  ([21545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part019 : ℚ :=
  (1701240173 : ℚ) / 250730360608112640

def SurrogateDiagonalTailChunk001Sub000Block122Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21545
    = surrogateDiagTailX0RatChunk001Sub000Block122Part019

theorem surrogateDiagonalTailChunk001Sub000Block122Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part019] using hcert

def TailChunk001Sub000Block122Part020SupportExplicit : Finset ℕ :=
  ([21547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part020 : ℚ :=
  (249314603425 : ℚ) / 465880577739088447488

def SurrogateDiagonalTailChunk001Sub000Block122Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21547
    = surrogateDiagTailX0RatChunk001Sub000Block122Part020

theorem surrogateDiagonalTailChunk001Sub000Block122Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part020] using hcert

def TailChunk001Sub000Block122Part021SupportExplicit : Finset ℕ :=
  ([21549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part021 : ℚ :=
  (120348809143 : ℚ) / 2891992855970611200

def SurrogateDiagonalTailChunk001Sub000Block122Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21549
    = surrogateDiagTailX0RatChunk001Sub000Block122Part021

theorem surrogateDiagonalTailChunk001Sub000Block122Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part021] using hcert

def TailChunk001Sub000Block122Part022SupportExplicit : Finset ℕ :=
  ([21551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part022 : ℚ :=
  (280425870775 : ℚ) / 449594486917338267648

def SurrogateDiagonalTailChunk001Sub000Block122Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21551
    = surrogateDiagTailX0RatChunk001Sub000Block122Part022

theorem surrogateDiagonalTailChunk001Sub000Block122Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part022] using hcert

def TailChunk001Sub000Block122Part023SupportExplicit : Finset ℕ :=
  ([21553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part023 : ℚ :=
  (592949244575 : ℚ) / 145437475253985774144

def SurrogateDiagonalTailChunk001Sub000Block122Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21553
    = surrogateDiagTailX0RatChunk001Sub000Block122Part023

theorem surrogateDiagonalTailChunk001Sub000Block122Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part023] using hcert

def TailChunk001Sub000Block122Part024SupportExplicit : Finset ℕ :=
  ([21554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block122Part024 : ℚ :=
  (260589538375 : ℚ) / 24370991051108548608

def SurrogateDiagonalTailChunk001Sub000Block122Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21554
    = surrogateDiagTailX0RatChunk001Sub000Block122Part024

theorem surrogateDiagonalTailChunk001Sub000Block122Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block122Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block122Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block122Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block122Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block122Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block122HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block122Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block122Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block122Part000
    + surrogateDiagTailX0RatChunk001Sub000Block122Part001
    + surrogateDiagTailX0RatChunk001Sub000Block122Part002
    + surrogateDiagTailX0RatChunk001Sub000Block122Part003
    + surrogateDiagTailX0RatChunk001Sub000Block122Part004
    + surrogateDiagTailX0RatChunk001Sub000Block122Part005
    + surrogateDiagTailX0RatChunk001Sub000Block122Part006
    + surrogateDiagTailX0RatChunk001Sub000Block122Part007
    + surrogateDiagTailX0RatChunk001Sub000Block122Part008
    + surrogateDiagTailX0RatChunk001Sub000Block122Part009

def surrogateDiagonalTailChunk001Sub000Block122MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block122Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block122Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block122Part010
    + surrogateDiagTailX0RatChunk001Sub000Block122Part011
    + surrogateDiagTailX0RatChunk001Sub000Block122Part012
    + surrogateDiagTailX0RatChunk001Sub000Block122Part013
    + surrogateDiagTailX0RatChunk001Sub000Block122Part014
    + surrogateDiagTailX0RatChunk001Sub000Block122Part015
    + surrogateDiagTailX0RatChunk001Sub000Block122Part016
    + surrogateDiagTailX0RatChunk001Sub000Block122Part017
    + surrogateDiagTailX0RatChunk001Sub000Block122Part018
    + surrogateDiagTailX0RatChunk001Sub000Block122Part019

def surrogateDiagonalTailChunk001Sub000Block122TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block122Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block122Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block122Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block122Part020
    + surrogateDiagTailX0RatChunk001Sub000Block122Part021
    + surrogateDiagTailX0RatChunk001Sub000Block122Part022
    + surrogateDiagTailX0RatChunk001Sub000Block122Part023
    + surrogateDiagTailX0RatChunk001Sub000Block122Part024

def surrogateDiagonalTailChunk001Sub000Block122Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block122HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block122MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block122TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block122 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block122Part000
    + surrogateDiagTailX0RatChunk001Sub000Block122Part001
    + surrogateDiagTailX0RatChunk001Sub000Block122Part002
    + surrogateDiagTailX0RatChunk001Sub000Block122Part003
    + surrogateDiagTailX0RatChunk001Sub000Block122Part004
    + surrogateDiagTailX0RatChunk001Sub000Block122Part005
    + surrogateDiagTailX0RatChunk001Sub000Block122Part006
    + surrogateDiagTailX0RatChunk001Sub000Block122Part007
    + surrogateDiagTailX0RatChunk001Sub000Block122Part008
    + surrogateDiagTailX0RatChunk001Sub000Block122Part009
    + surrogateDiagTailX0RatChunk001Sub000Block122Part010
    + surrogateDiagTailX0RatChunk001Sub000Block122Part011
    + surrogateDiagTailX0RatChunk001Sub000Block122Part012
    + surrogateDiagTailX0RatChunk001Sub000Block122Part013
    + surrogateDiagTailX0RatChunk001Sub000Block122Part014
    + surrogateDiagTailX0RatChunk001Sub000Block122Part015
    + surrogateDiagTailX0RatChunk001Sub000Block122Part016
    + surrogateDiagTailX0RatChunk001Sub000Block122Part017
    + surrogateDiagTailX0RatChunk001Sub000Block122Part018
    + surrogateDiagTailX0RatChunk001Sub000Block122Part019
    + surrogateDiagTailX0RatChunk001Sub000Block122Part020
    + surrogateDiagTailX0RatChunk001Sub000Block122Part021
    + surrogateDiagTailX0RatChunk001Sub000Block122Part022
    + surrogateDiagTailX0RatChunk001Sub000Block122Part023
    + surrogateDiagTailX0RatChunk001Sub000Block122Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block122_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block122Head + surrogateDiagTailX0RatChunk001Sub000Block122Mid + surrogateDiagTailX0RatChunk001Sub000Block122Tail =
      surrogateDiagTailX0RatChunk001Sub000Block122 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block122Head surrogateDiagTailX0RatChunk001Sub000Block122Mid surrogateDiagTailX0RatChunk001Sub000Block122Tail surrogateDiagTailX0RatChunk001Sub000Block122
  ring

def SurrogateDiagonalTailChunk001Sub000Block122HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block122HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block122Head

def SurrogateDiagonalTailChunk001Sub000Block122MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block122MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block122Mid

def SurrogateDiagonalTailChunk001Sub000Block122TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block122TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block122Tail

theorem surrogateDiagonalTailChunk001Sub000Block122_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block122HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block122MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block122TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block122Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block122 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block122HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block122MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block122TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block122Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block122_eq_head_add_mid_add_tail

/-- Block 123 covers tail-support indices [13075,13100) and q from 21557 to 21594. -/

def TailChunk001Sub000Block123Part000SupportExplicit : Finset ℕ :=
  ([21557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21557
    = surrogateDiagTailX0RatChunk001Sub000Block123Part000

theorem surrogateDiagonalTailChunk001Sub000Block123Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part000] using hcert

def TailChunk001Sub000Block123Part001SupportExplicit : Finset ℕ :=
  ([21558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part001 : ℚ :=
  (201757274425 : ℚ) / 1665068719867502592

def SurrogateDiagonalTailChunk001Sub000Block123Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21558
    = surrogateDiagTailX0RatChunk001Sub000Block123Part001

theorem surrogateDiagonalTailChunk001Sub000Block123Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part001] using hcert

def TailChunk001Sub000Block123Part002SupportExplicit : Finset ℕ :=
  ([21559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21559
    = surrogateDiagTailX0RatChunk001Sub000Block123Part002

theorem surrogateDiagonalTailChunk001Sub000Block123Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part002] using hcert

def TailChunk001Sub000Block123Part003SupportExplicit : Finset ℕ :=
  ([21561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part003 : ℚ :=
  (1614018628925 : ℚ) / 53341558115411724864

def SurrogateDiagonalTailChunk001Sub000Block123Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21561
    = surrogateDiagTailX0RatChunk001Sub000Block123Part003

theorem surrogateDiagonalTailChunk001Sub000Block123Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part003] using hcert

def TailChunk001Sub000Block123Part004SupportExplicit : Finset ℕ :=
  ([21562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21562
    = surrogateDiagTailX0RatChunk001Sub000Block123Part004

theorem surrogateDiagonalTailChunk001Sub000Block123Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part004] using hcert

def TailChunk001Sub000Block123Part005SupportExplicit : Finset ℕ :=
  ([21563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21563
    = surrogateDiagTailX0RatChunk001Sub000Block123Part005

theorem surrogateDiagonalTailChunk001Sub000Block123Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part005] using hcert

def TailChunk001Sub000Block123Part006SupportExplicit : Finset ℕ :=
  ([21565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part006 : ℚ :=
  (586466488075 : ℚ) / 43825876429541548032

def SurrogateDiagonalTailChunk001Sub000Block123Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21565
    = surrogateDiagTailX0RatChunk001Sub000Block123Part006

theorem surrogateDiagonalTailChunk001Sub000Block123Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part006] using hcert

def TailChunk001Sub000Block123Part007SupportExplicit : Finset ℕ :=
  ([21566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part007 : ℚ :=
  (624833691 : ℚ) / 201085488458547200

def SurrogateDiagonalTailChunk001Sub000Block123Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21566
    = surrogateDiagTailX0RatChunk001Sub000Block123Part007

theorem surrogateDiagonalTailChunk001Sub000Block123Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part007] using hcert

def TailChunk001Sub000Block123Part008SupportExplicit : Finset ℕ :=
  ([21567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part008 : ℚ :=
  (667531844875 : ℚ) / 9949362322328911872

def SurrogateDiagonalTailChunk001Sub000Block123Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21567
    = surrogateDiagTailX0RatChunk001Sub000Block123Part008

theorem surrogateDiagonalTailChunk001Sub000Block123Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part008] using hcert

def TailChunk001Sub000Block123Part009SupportExplicit : Finset ℕ :=
  ([21569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21569
    = surrogateDiagTailX0RatChunk001Sub000Block123Part009

theorem surrogateDiagonalTailChunk001Sub000Block123Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part009] using hcert

def TailChunk001Sub000Block123Part010SupportExplicit : Finset ℕ :=
  ([21570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part010 : ℚ :=
  (1001210821075 : ℚ) / 2721977831167131648

def SurrogateDiagonalTailChunk001Sub000Block123Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21570
    = surrogateDiagTailX0RatChunk001Sub000Block123Part010

theorem surrogateDiagonalTailChunk001Sub000Block123Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part010] using hcert

def TailChunk001Sub000Block123Part011SupportExplicit : Finset ℕ :=
  ([21571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part011 : ℚ :=
  (18656847311 : ℚ) / 6141581680449945600

def SurrogateDiagonalTailChunk001Sub000Block123Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21571
    = surrogateDiagTailX0RatChunk001Sub000Block123Part011

theorem surrogateDiagonalTailChunk001Sub000Block123Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part011] using hcert

def TailChunk001Sub000Block123Part012SupportExplicit : Finset ℕ :=
  ([21574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part012 : ℚ :=
  (50103457325 : ℚ) / 1309500415967090688

def SurrogateDiagonalTailChunk001Sub000Block123Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21574
    = surrogateDiagTailX0RatChunk001Sub000Block123Part012

theorem surrogateDiagonalTailChunk001Sub000Block123Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part012] using hcert

def TailChunk001Sub000Block123Part013SupportExplicit : Finset ℕ :=
  ([21577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21577
    = surrogateDiagTailX0RatChunk001Sub000Block123Part013

theorem surrogateDiagonalTailChunk001Sub000Block123Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part013] using hcert

def TailChunk001Sub000Block123Part014SupportExplicit : Finset ℕ :=
  ([21578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21578
    = surrogateDiagTailX0RatChunk001Sub000Block123Part014

theorem surrogateDiagonalTailChunk001Sub000Block123Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part014] using hcert

def TailChunk001Sub000Block123Part015SupportExplicit : Finset ℕ :=
  ([21579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part015 : ℚ :=
  (808357251925 : ℚ) / 26759966481296596992

def SurrogateDiagonalTailChunk001Sub000Block123Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21579
    = surrogateDiagTailX0RatChunk001Sub000Block123Part015

theorem surrogateDiagonalTailChunk001Sub000Block123Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part015] using hcert

def TailChunk001Sub000Block123Part016SupportExplicit : Finset ℕ :=
  ([21581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part016 : ℚ :=
  (595545153925 : ℚ) / 292389921006233298048

def SurrogateDiagonalTailChunk001Sub000Block123Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21581
    = surrogateDiagTailX0RatChunk001Sub000Block123Part016

theorem surrogateDiagonalTailChunk001Sub000Block123Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part016] using hcert

def TailChunk001Sub000Block123Part017SupportExplicit : Finset ℕ :=
  ([21583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part017 : ℚ :=
  (751605551 : ℚ) / 4102072580757258240

def SurrogateDiagonalTailChunk001Sub000Block123Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21583
    = surrogateDiagTailX0RatChunk001Sub000Block123Part017

theorem surrogateDiagonalTailChunk001Sub000Block123Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part017] using hcert

def TailChunk001Sub000Block123Part018SupportExplicit : Finset ℕ :=
  ([21585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part018 : ℚ :=
  (226370172375 : ℚ) / 3649565016830009344

def SurrogateDiagonalTailChunk001Sub000Block123Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21585
    = surrogateDiagTailX0RatChunk001Sub000Block123Part018

theorem surrogateDiagonalTailChunk001Sub000Block123Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part018] using hcert

def TailChunk001Sub000Block123Part019SupportExplicit : Finset ℕ :=
  ([21586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part019 : ℚ :=
  (871516669 : ℚ) / 303937337812500000

def SurrogateDiagonalTailChunk001Sub000Block123Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21586
    = surrogateDiagTailX0RatChunk001Sub000Block123Part019

theorem surrogateDiagonalTailChunk001Sub000Block123Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part019] using hcert

def TailChunk001Sub000Block123Part020SupportExplicit : Finset ℕ :=
  ([21587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21587
    = surrogateDiagTailX0RatChunk001Sub000Block123Part020

theorem surrogateDiagonalTailChunk001Sub000Block123Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part020] using hcert

def TailChunk001Sub000Block123Part021SupportExplicit : Finset ℕ :=
  ([21589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block123Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21589
    = surrogateDiagTailX0RatChunk001Sub000Block123Part021

theorem surrogateDiagonalTailChunk001Sub000Block123Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part021] using hcert

def TailChunk001Sub000Block123Part022SupportExplicit : Finset ℕ :=
  ([21590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part022 : ℚ :=
  (2110194725 : ℚ) / 32635023148449792

def SurrogateDiagonalTailChunk001Sub000Block123Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21590
    = surrogateDiagTailX0RatChunk001Sub000Block123Part022

theorem surrogateDiagonalTailChunk001Sub000Block123Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part022] using hcert

def TailChunk001Sub000Block123Part023SupportExplicit : Finset ℕ :=
  ([21593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part023 : ℚ :=
  (11046216139 : ℚ) / 2624924880000000000

def SurrogateDiagonalTailChunk001Sub000Block123Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21593
    = surrogateDiagTailX0RatChunk001Sub000Block123Part023

theorem surrogateDiagonalTailChunk001Sub000Block123Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part023] using hcert

def TailChunk001Sub000Block123Part024SupportExplicit : Finset ℕ :=
  ([21594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block123Part024 : ℚ :=
  (31720622981 : ℚ) / 117352896414105600

def SurrogateDiagonalTailChunk001Sub000Block123Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21594
    = surrogateDiagTailX0RatChunk001Sub000Block123Part024

theorem surrogateDiagonalTailChunk001Sub000Block123Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block123Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block123Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block123Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block123Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block123Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block123HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block123Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block123Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block123Part000
    + surrogateDiagTailX0RatChunk001Sub000Block123Part001
    + surrogateDiagTailX0RatChunk001Sub000Block123Part002
    + surrogateDiagTailX0RatChunk001Sub000Block123Part003
    + surrogateDiagTailX0RatChunk001Sub000Block123Part004
    + surrogateDiagTailX0RatChunk001Sub000Block123Part005
    + surrogateDiagTailX0RatChunk001Sub000Block123Part006
    + surrogateDiagTailX0RatChunk001Sub000Block123Part007
    + surrogateDiagTailX0RatChunk001Sub000Block123Part008
    + surrogateDiagTailX0RatChunk001Sub000Block123Part009

def surrogateDiagonalTailChunk001Sub000Block123MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block123Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block123Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block123Part010
    + surrogateDiagTailX0RatChunk001Sub000Block123Part011
    + surrogateDiagTailX0RatChunk001Sub000Block123Part012
    + surrogateDiagTailX0RatChunk001Sub000Block123Part013
    + surrogateDiagTailX0RatChunk001Sub000Block123Part014
    + surrogateDiagTailX0RatChunk001Sub000Block123Part015
    + surrogateDiagTailX0RatChunk001Sub000Block123Part016
    + surrogateDiagTailX0RatChunk001Sub000Block123Part017
    + surrogateDiagTailX0RatChunk001Sub000Block123Part018
    + surrogateDiagTailX0RatChunk001Sub000Block123Part019

def surrogateDiagonalTailChunk001Sub000Block123TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block123Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block123Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block123Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block123Part020
    + surrogateDiagTailX0RatChunk001Sub000Block123Part021
    + surrogateDiagTailX0RatChunk001Sub000Block123Part022
    + surrogateDiagTailX0RatChunk001Sub000Block123Part023
    + surrogateDiagTailX0RatChunk001Sub000Block123Part024

def surrogateDiagonalTailChunk001Sub000Block123Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block123HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block123MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block123TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block123 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block123Part000
    + surrogateDiagTailX0RatChunk001Sub000Block123Part001
    + surrogateDiagTailX0RatChunk001Sub000Block123Part002
    + surrogateDiagTailX0RatChunk001Sub000Block123Part003
    + surrogateDiagTailX0RatChunk001Sub000Block123Part004
    + surrogateDiagTailX0RatChunk001Sub000Block123Part005
    + surrogateDiagTailX0RatChunk001Sub000Block123Part006
    + surrogateDiagTailX0RatChunk001Sub000Block123Part007
    + surrogateDiagTailX0RatChunk001Sub000Block123Part008
    + surrogateDiagTailX0RatChunk001Sub000Block123Part009
    + surrogateDiagTailX0RatChunk001Sub000Block123Part010
    + surrogateDiagTailX0RatChunk001Sub000Block123Part011
    + surrogateDiagTailX0RatChunk001Sub000Block123Part012
    + surrogateDiagTailX0RatChunk001Sub000Block123Part013
    + surrogateDiagTailX0RatChunk001Sub000Block123Part014
    + surrogateDiagTailX0RatChunk001Sub000Block123Part015
    + surrogateDiagTailX0RatChunk001Sub000Block123Part016
    + surrogateDiagTailX0RatChunk001Sub000Block123Part017
    + surrogateDiagTailX0RatChunk001Sub000Block123Part018
    + surrogateDiagTailX0RatChunk001Sub000Block123Part019
    + surrogateDiagTailX0RatChunk001Sub000Block123Part020
    + surrogateDiagTailX0RatChunk001Sub000Block123Part021
    + surrogateDiagTailX0RatChunk001Sub000Block123Part022
    + surrogateDiagTailX0RatChunk001Sub000Block123Part023
    + surrogateDiagTailX0RatChunk001Sub000Block123Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block123_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block123Head + surrogateDiagTailX0RatChunk001Sub000Block123Mid + surrogateDiagTailX0RatChunk001Sub000Block123Tail =
      surrogateDiagTailX0RatChunk001Sub000Block123 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block123Head surrogateDiagTailX0RatChunk001Sub000Block123Mid surrogateDiagTailX0RatChunk001Sub000Block123Tail surrogateDiagTailX0RatChunk001Sub000Block123
  ring

def SurrogateDiagonalTailChunk001Sub000Block123HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block123HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block123Head

def SurrogateDiagonalTailChunk001Sub000Block123MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block123MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block123Mid

def SurrogateDiagonalTailChunk001Sub000Block123TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block123TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block123Tail

theorem surrogateDiagonalTailChunk001Sub000Block123_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block123HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block123MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block123TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block123Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block123 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block123HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block123MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block123TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block123Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block123_eq_head_add_mid_add_tail

/-- Block 124 covers tail-support indices [13100,13125) and q from 21595 to 21633. -/

def TailChunk001Sub000Block124Part000SupportExplicit : Finset ℕ :=
  ([21595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part000 : ℚ :=
  (1383229720375 : ℚ) / 119452343479113351168

def SurrogateDiagonalTailChunk001Sub000Block124Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21595
    = surrogateDiagTailX0RatChunk001Sub000Block124Part000

theorem surrogateDiagonalTailChunk001Sub000Block124Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part000] using hcert

def TailChunk001Sub000Block124Part001SupportExplicit : Finset ℕ :=
  ([21597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part001 : ℚ :=
  (3140879595925 : ℚ) / 88808787539227312128

def SurrogateDiagonalTailChunk001Sub000Block124Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21597
    = surrogateDiagTailX0RatChunk001Sub000Block124Part001

theorem surrogateDiagonalTailChunk001Sub000Block124Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part001] using hcert

def TailChunk001Sub000Block124Part002SupportExplicit : Finset ℕ :=
  ([21598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block124Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21598
    = surrogateDiagTailX0RatChunk001Sub000Block124Part002

theorem surrogateDiagonalTailChunk001Sub000Block124Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part002] using hcert

def TailChunk001Sub000Block124Part003SupportExplicit : Finset ℕ :=
  ([21599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block124Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21599
    = surrogateDiagTailX0RatChunk001Sub000Block124Part003

theorem surrogateDiagonalTailChunk001Sub000Block124Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part003] using hcert

def TailChunk001Sub000Block124Part004SupportExplicit : Finset ℕ :=
  ([21601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block124Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21601
    = surrogateDiagTailX0RatChunk001Sub000Block124Part004

theorem surrogateDiagonalTailChunk001Sub000Block124Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part004] using hcert

def TailChunk001Sub000Block124Part005SupportExplicit : Finset ℕ :=
  ([21602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part005 : ℚ :=
  (8287537825 : ℚ) / 339293543521436352

def SurrogateDiagonalTailChunk001Sub000Block124Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21602
    = surrogateDiagTailX0RatChunk001Sub000Block124Part005

theorem surrogateDiagonalTailChunk001Sub000Block124Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part005] using hcert

def TailChunk001Sub000Block124Part006SupportExplicit : Finset ℕ :=
  ([21603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part006 : ℚ :=
  (786398323975 : ℚ) / 21436015873716122112

def SurrogateDiagonalTailChunk001Sub000Block124Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21603
    = surrogateDiagTailX0RatChunk001Sub000Block124Part006

theorem surrogateDiagonalTailChunk001Sub000Block124Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part006] using hcert

def TailChunk001Sub000Block124Part007SupportExplicit : Finset ℕ :=
  ([21605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part007 : ℚ :=
  (425446739475 : ℚ) / 62925193023582109696

def SurrogateDiagonalTailChunk001Sub000Block124Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21605
    = surrogateDiagTailX0RatChunk001Sub000Block124Part007

theorem surrogateDiagonalTailChunk001Sub000Block124Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part007] using hcert

def TailChunk001Sub000Block124Part008SupportExplicit : Finset ℕ :=
  ([21606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part008 : ℚ :=
  (1540182019975 : ℚ) / 4814022923675762688

def SurrogateDiagonalTailChunk001Sub000Block124Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21606
    = surrogateDiagTailX0RatChunk001Sub000Block124Part008

theorem surrogateDiagonalTailChunk001Sub000Block124Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part008] using hcert

def TailChunk001Sub000Block124Part009SupportExplicit : Finset ℕ :=
  ([21607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part009 : ℚ :=
  (7070764051 : ℚ) / 3398065717248000000

def SurrogateDiagonalTailChunk001Sub000Block124Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21607
    = surrogateDiagTailX0RatChunk001Sub000Block124Part009

theorem surrogateDiagonalTailChunk001Sub000Block124Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part009] using hcert

def TailChunk001Sub000Block124Part010SupportExplicit : Finset ℕ :=
  ([21610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part010 : ℚ :=
  (7791117823 : ℚ) / 185789243090534400

def SurrogateDiagonalTailChunk001Sub000Block124Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21610
    = surrogateDiagTailX0RatChunk001Sub000Block124Part010

theorem surrogateDiagonalTailChunk001Sub000Block124Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part010] using hcert

def TailChunk001Sub000Block124Part011SupportExplicit : Finset ℕ :=
  ([21611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block124Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21611
    = surrogateDiagTailX0RatChunk001Sub000Block124Part011

theorem surrogateDiagonalTailChunk001Sub000Block124Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part011] using hcert

def TailChunk001Sub000Block124Part012SupportExplicit : Finset ℕ :=
  ([21613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block124Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21613
    = surrogateDiagTailX0RatChunk001Sub000Block124Part012

theorem surrogateDiagonalTailChunk001Sub000Block124Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part012] using hcert

def TailChunk001Sub000Block124Part013SupportExplicit : Finset ℕ :=
  ([21614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part013 : ℚ :=
  (160632091 : ℚ) / 78920590962000000

def SurrogateDiagonalTailChunk001Sub000Block124Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21614
    = surrogateDiagTailX0RatChunk001Sub000Block124Part013

theorem surrogateDiagonalTailChunk001Sub000Block124Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part013] using hcert

def TailChunk001Sub000Block124Part014SupportExplicit : Finset ℕ :=
  ([21615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part014 : ℚ :=
  (52191911651 : ℚ) / 585046265856000000

def SurrogateDiagonalTailChunk001Sub000Block124Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21615
    = surrogateDiagTailX0RatChunk001Sub000Block124Part014

theorem surrogateDiagonalTailChunk001Sub000Block124Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part014] using hcert

def TailChunk001Sub000Block124Part015SupportExplicit : Finset ℕ :=
  ([21617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block124Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21617
    = surrogateDiagTailX0RatChunk001Sub000Block124Part015

theorem surrogateDiagonalTailChunk001Sub000Block124Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part015] using hcert

def TailChunk001Sub000Block124Part016SupportExplicit : Finset ℕ :=
  ([21619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part016 : ℚ :=
  (130366692925 : ℚ) / 98904472164391629312

def SurrogateDiagonalTailChunk001Sub000Block124Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21619
    = surrogateDiagTailX0RatChunk001Sub000Block124Part016

theorem surrogateDiagonalTailChunk001Sub000Block124Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part016] using hcert

def TailChunk001Sub000Block124Part017SupportExplicit : Finset ℕ :=
  ([21621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part017 : ℚ :=
  (1623013628675 : ℚ) / 53937880532264568384

def SurrogateDiagonalTailChunk001Sub000Block124Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21621
    = surrogateDiagTailX0RatChunk001Sub000Block124Part017

theorem surrogateDiagonalTailChunk001Sub000Block124Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part017] using hcert

def TailChunk001Sub000Block124Part018SupportExplicit : Finset ℕ :=
  ([21622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part018 : ℚ :=
  (93403717925 : ℚ) / 13660928757662367744

def SurrogateDiagonalTailChunk001Sub000Block124Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21622
    = surrogateDiagTailX0RatChunk001Sub000Block124Part018

theorem surrogateDiagonalTailChunk001Sub000Block124Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part018] using hcert

def TailChunk001Sub000Block124Part019SupportExplicit : Finset ℕ :=
  ([21623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part019 : ℚ :=
  (596802224075 : ℚ) / 147336731540345585664

def SurrogateDiagonalTailChunk001Sub000Block124Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21623
    = surrogateDiagTailX0RatChunk001Sub000Block124Part019

theorem surrogateDiagonalTailChunk001Sub000Block124Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part019] using hcert

def TailChunk001Sub000Block124Part020SupportExplicit : Finset ℕ :=
  ([21626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part020 : ℚ :=
  (243389801 : ℚ) / 18602135222627904

def SurrogateDiagonalTailChunk001Sub000Block124Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21626
    = surrogateDiagTailX0RatChunk001Sub000Block124Part020

theorem surrogateDiagonalTailChunk001Sub000Block124Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part020] using hcert

def TailChunk001Sub000Block124Part021SupportExplicit : Finset ℕ :=
  ([21629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part021 : ℚ :=
  (5730651875 : ℚ) / 18301012805196825984

def SurrogateDiagonalTailChunk001Sub000Block124Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21629
    = surrogateDiagTailX0RatChunk001Sub000Block124Part021

theorem surrogateDiagonalTailChunk001Sub000Block124Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part021] using hcert

def TailChunk001Sub000Block124Part022SupportExplicit : Finset ℕ :=
  ([21630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part022 : ℚ :=
  (73005299525 : ℚ) / 84516902898499584

def SurrogateDiagonalTailChunk001Sub000Block124Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21630
    = surrogateDiagTailX0RatChunk001Sub000Block124Part022

theorem surrogateDiagonalTailChunk001Sub000Block124Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part022] using hcert

def TailChunk001Sub000Block124Part023SupportExplicit : Finset ℕ :=
  ([21631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part023 : ℚ :=
  (97738885075 : ℚ) / 515850301658961543168

def SurrogateDiagonalTailChunk001Sub000Block124Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21631
    = surrogateDiagTailX0RatChunk001Sub000Block124Part023

theorem surrogateDiagonalTailChunk001Sub000Block124Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part023] using hcert

def TailChunk001Sub000Block124Part024SupportExplicit : Finset ℕ :=
  ([21633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block124Part024 : ℚ :=
  (265276021 : ℚ) / 8825753868214080

def SurrogateDiagonalTailChunk001Sub000Block124Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21633
    = surrogateDiagTailX0RatChunk001Sub000Block124Part024

theorem surrogateDiagonalTailChunk001Sub000Block124Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block124Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block124Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block124Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block124Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block124Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block124HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block124Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block124Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block124Part000
    + surrogateDiagTailX0RatChunk001Sub000Block124Part001
    + surrogateDiagTailX0RatChunk001Sub000Block124Part002
    + surrogateDiagTailX0RatChunk001Sub000Block124Part003
    + surrogateDiagTailX0RatChunk001Sub000Block124Part004
    + surrogateDiagTailX0RatChunk001Sub000Block124Part005
    + surrogateDiagTailX0RatChunk001Sub000Block124Part006
    + surrogateDiagTailX0RatChunk001Sub000Block124Part007
    + surrogateDiagTailX0RatChunk001Sub000Block124Part008
    + surrogateDiagTailX0RatChunk001Sub000Block124Part009

def surrogateDiagonalTailChunk001Sub000Block124MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block124Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block124Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block124Part010
    + surrogateDiagTailX0RatChunk001Sub000Block124Part011
    + surrogateDiagTailX0RatChunk001Sub000Block124Part012
    + surrogateDiagTailX0RatChunk001Sub000Block124Part013
    + surrogateDiagTailX0RatChunk001Sub000Block124Part014
    + surrogateDiagTailX0RatChunk001Sub000Block124Part015
    + surrogateDiagTailX0RatChunk001Sub000Block124Part016
    + surrogateDiagTailX0RatChunk001Sub000Block124Part017
    + surrogateDiagTailX0RatChunk001Sub000Block124Part018
    + surrogateDiagTailX0RatChunk001Sub000Block124Part019

def surrogateDiagonalTailChunk001Sub000Block124TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block124Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block124Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block124Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block124Part020
    + surrogateDiagTailX0RatChunk001Sub000Block124Part021
    + surrogateDiagTailX0RatChunk001Sub000Block124Part022
    + surrogateDiagTailX0RatChunk001Sub000Block124Part023
    + surrogateDiagTailX0RatChunk001Sub000Block124Part024

def surrogateDiagonalTailChunk001Sub000Block124Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block124HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block124MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block124TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block124 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block124Part000
    + surrogateDiagTailX0RatChunk001Sub000Block124Part001
    + surrogateDiagTailX0RatChunk001Sub000Block124Part002
    + surrogateDiagTailX0RatChunk001Sub000Block124Part003
    + surrogateDiagTailX0RatChunk001Sub000Block124Part004
    + surrogateDiagTailX0RatChunk001Sub000Block124Part005
    + surrogateDiagTailX0RatChunk001Sub000Block124Part006
    + surrogateDiagTailX0RatChunk001Sub000Block124Part007
    + surrogateDiagTailX0RatChunk001Sub000Block124Part008
    + surrogateDiagTailX0RatChunk001Sub000Block124Part009
    + surrogateDiagTailX0RatChunk001Sub000Block124Part010
    + surrogateDiagTailX0RatChunk001Sub000Block124Part011
    + surrogateDiagTailX0RatChunk001Sub000Block124Part012
    + surrogateDiagTailX0RatChunk001Sub000Block124Part013
    + surrogateDiagTailX0RatChunk001Sub000Block124Part014
    + surrogateDiagTailX0RatChunk001Sub000Block124Part015
    + surrogateDiagTailX0RatChunk001Sub000Block124Part016
    + surrogateDiagTailX0RatChunk001Sub000Block124Part017
    + surrogateDiagTailX0RatChunk001Sub000Block124Part018
    + surrogateDiagTailX0RatChunk001Sub000Block124Part019
    + surrogateDiagTailX0RatChunk001Sub000Block124Part020
    + surrogateDiagTailX0RatChunk001Sub000Block124Part021
    + surrogateDiagTailX0RatChunk001Sub000Block124Part022
    + surrogateDiagTailX0RatChunk001Sub000Block124Part023
    + surrogateDiagTailX0RatChunk001Sub000Block124Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block124_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block124Head + surrogateDiagTailX0RatChunk001Sub000Block124Mid + surrogateDiagTailX0RatChunk001Sub000Block124Tail =
      surrogateDiagTailX0RatChunk001Sub000Block124 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block124Head surrogateDiagTailX0RatChunk001Sub000Block124Mid surrogateDiagTailX0RatChunk001Sub000Block124Tail surrogateDiagTailX0RatChunk001Sub000Block124
  ring

def SurrogateDiagonalTailChunk001Sub000Block124HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block124HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block124Head

def SurrogateDiagonalTailChunk001Sub000Block124MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block124MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block124Mid

def SurrogateDiagonalTailChunk001Sub000Block124TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block124TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block124Tail

theorem surrogateDiagonalTailChunk001Sub000Block124_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block124HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block124MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block124TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block124Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block124 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block124HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block124MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block124TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block124Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block124_eq_head_add_mid_add_tail

/-- Block 125 covers tail-support indices [13125,13150) and q from 21634 to 21674. -/

def TailChunk001Sub000Block125Part000SupportExplicit : Finset ℕ :=
  ([21634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part000 : ℚ :=
  (5037412375 : ℚ) / 1226364307172831232

def SurrogateDiagonalTailChunk001Sub000Block125Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21634
    = surrogateDiagTailX0RatChunk001Sub000Block125Part000

theorem surrogateDiagonalTailChunk001Sub000Block125Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part000] using hcert

def TailChunk001Sub000Block125Part001SupportExplicit : Finset ℕ :=
  ([21635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part001 : ℚ :=
  (1170892896625 : ℚ) / 224188269458826774528

def SurrogateDiagonalTailChunk001Sub000Block125Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21635
    = surrogateDiagTailX0RatChunk001Sub000Block125Part001

theorem surrogateDiagonalTailChunk001Sub000Block125Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part001] using hcert

def TailChunk001Sub000Block125Part002SupportExplicit : Finset ℕ :=
  ([21637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part002 : ℚ :=
  (6311610203 : ℚ) / 885281660928000000

def SurrogateDiagonalTailChunk001Sub000Block125Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21637
    = surrogateDiagTailX0RatChunk001Sub000Block125Part002

theorem surrogateDiagonalTailChunk001Sub000Block125Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part002] using hcert

def TailChunk001Sub000Block125Part003SupportExplicit : Finset ℕ :=
  ([21638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part003 : ℚ :=
  (158689307 : ℚ) / 40972347454924800

def SurrogateDiagonalTailChunk001Sub000Block125Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21638
    = surrogateDiagTailX0RatChunk001Sub000Block125Part003

theorem surrogateDiagonalTailChunk001Sub000Block125Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part003] using hcert

def TailChunk001Sub000Block125Part004SupportExplicit : Finset ℕ :=
  ([21639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part004 : ℚ :=
  (101607312725 : ℚ) / 3382359266019806784

def SurrogateDiagonalTailChunk001Sub000Block125Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21639
    = surrogateDiagTailX0RatChunk001Sub000Block125Part004

theorem surrogateDiagonalTailChunk001Sub000Block125Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part004] using hcert

def TailChunk001Sub000Block125Part005SupportExplicit : Finset ℕ :=
  ([21641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part005 : ℚ :=
  (811513782175 : ℚ) / 326416836970621698048

def SurrogateDiagonalTailChunk001Sub000Block125Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21641
    = surrogateDiagTailX0RatChunk001Sub000Block125Part005

theorem surrogateDiagonalTailChunk001Sub000Block125Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part005] using hcert

def TailChunk001Sub000Block125Part006SupportExplicit : Finset ℕ :=
  ([21642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part006 : ℚ :=
  (812852091725 : ℚ) / 3382359266019806784

def SurrogateDiagonalTailChunk001Sub000Block125Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21642
    = surrogateDiagTailX0RatChunk001Sub000Block125Part006

theorem surrogateDiagonalTailChunk001Sub000Block125Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part006] using hcert

def TailChunk001Sub000Block125Part007SupportExplicit : Finset ℕ :=
  ([21643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part007 : ℚ :=
  (3770253297 : ℚ) / 6097723579981158400

def SurrogateDiagonalTailChunk001Sub000Block125Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21643
    = surrogateDiagTailX0RatChunk001Sub000Block125Part007

theorem surrogateDiagonalTailChunk001Sub000Block125Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part007] using hcert

def TailChunk001Sub000Block125Part008SupportExplicit : Finset ℕ :=
  ([21646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part008 : ℚ :=
  (8341164875 : ℚ) / 3957955582815277056

def SurrogateDiagonalTailChunk001Sub000Block125Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21646
    = surrogateDiagTailX0RatChunk001Sub000Block125Part008

theorem surrogateDiagonalTailChunk001Sub000Block125Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part008] using hcert

def TailChunk001Sub000Block125Part009SupportExplicit : Finset ℕ :=
  ([21647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block125Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21647
    = surrogateDiagTailX0RatChunk001Sub000Block125Part009

theorem surrogateDiagonalTailChunk001Sub000Block125Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part009] using hcert

def TailChunk001Sub000Block125Part010SupportExplicit : Finset ℕ :=
  ([21649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block125Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21649
    = surrogateDiagTailX0RatChunk001Sub000Block125Part010

theorem surrogateDiagonalTailChunk001Sub000Block125Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part010] using hcert

def TailChunk001Sub000Block125Part011SupportExplicit : Finset ℕ :=
  ([21651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part011 : ℚ :=
  (5866002191 : ℚ) / 466864367885936640

def SurrogateDiagonalTailChunk001Sub000Block125Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21651
    = surrogateDiagTailX0RatChunk001Sub000Block125Part011

theorem surrogateDiagonalTailChunk001Sub000Block125Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part011] using hcert

def TailChunk001Sub000Block125Part012SupportExplicit : Finset ℕ :=
  ([21653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part012 : ℚ :=
  (135084414025 : ℚ) / 507765482699742592128

def SurrogateDiagonalTailChunk001Sub000Block125Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21653
    = surrogateDiagTailX0RatChunk001Sub000Block125Part012

theorem surrogateDiagonalTailChunk001Sub000Block125Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part012] using hcert

def TailChunk001Sub000Block125Part013SupportExplicit : Finset ℕ :=
  ([21655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part013 : ℚ :=
  (10091307509 : ℚ) / 1593506989670400000

def SurrogateDiagonalTailChunk001Sub000Block125Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21655
    = surrogateDiagTailX0RatChunk001Sub000Block125Part013

theorem surrogateDiagonalTailChunk001Sub000Block125Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part013] using hcert

def TailChunk001Sub000Block125Part014SupportExplicit : Finset ℕ :=
  ([21657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part014 : ℚ :=
  (41675 : ℚ) / 7238294402737536

def SurrogateDiagonalTailChunk001Sub000Block125Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21657
    = surrogateDiagTailX0RatChunk001Sub000Block125Part014

theorem surrogateDiagonalTailChunk001Sub000Block125Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part014] using hcert

def TailChunk001Sub000Block125Part015SupportExplicit : Finset ℕ :=
  ([21661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block125Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21661
    = surrogateDiagTailX0RatChunk001Sub000Block125Part015

theorem surrogateDiagonalTailChunk001Sub000Block125Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part015] using hcert

def TailChunk001Sub000Block125Part016SupportExplicit : Finset ℕ :=
  ([21662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block125Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21662
    = surrogateDiagTailX0RatChunk001Sub000Block125Part016

theorem surrogateDiagonalTailChunk001Sub000Block125Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part016] using hcert

def TailChunk001Sub000Block125Part017SupportExplicit : Finset ℕ :=
  ([21665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part017 : ℚ :=
  (145832532275 : ℚ) / 10084270346336231424

def SurrogateDiagonalTailChunk001Sub000Block125Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21665
    = surrogateDiagTailX0RatChunk001Sub000Block125Part017

theorem surrogateDiagonalTailChunk001Sub000Block125Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part017] using hcert

def TailChunk001Sub000Block125Part018SupportExplicit : Finset ℕ :=
  ([21666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part018 : ℚ :=
  (211791045925 : ℚ) / 1387637305300426752

def SurrogateDiagonalTailChunk001Sub000Block125Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21666
    = surrogateDiagTailX0RatChunk001Sub000Block125Part018

theorem surrogateDiagonalTailChunk001Sub000Block125Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part018] using hcert

def TailChunk001Sub000Block125Part019SupportExplicit : Finset ℕ :=
  ([21667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part019 : ℚ :=
  (1063411173 : ℚ) / 3341936959063731200

def SurrogateDiagonalTailChunk001Sub000Block125Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21667
    = surrogateDiagTailX0RatChunk001Sub000Block125Part019

theorem surrogateDiagonalTailChunk001Sub000Block125Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part019] using hcert

def TailChunk001Sub000Block125Part020SupportExplicit : Finset ℕ :=
  ([21669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part020 : ℚ :=
  (3269103491 : ℚ) / 1877646342625689600

def SurrogateDiagonalTailChunk001Sub000Block125Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21669
    = surrogateDiagTailX0RatChunk001Sub000Block125Part020

theorem surrogateDiagonalTailChunk001Sub000Block125Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part020] using hcert

def TailChunk001Sub000Block125Part021SupportExplicit : Finset ℕ :=
  ([21670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part021 : ℚ :=
  (5516285353 : ℚ) / 53982508390809600

def SurrogateDiagonalTailChunk001Sub000Block125Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21670
    = surrogateDiagTailX0RatChunk001Sub000Block125Part021

theorem surrogateDiagonalTailChunk001Sub000Block125Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part021] using hcert

def TailChunk001Sub000Block125Part022SupportExplicit : Finset ℕ :=
  ([21671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part022 : ℚ :=
  (1169557525 : ℚ) / 891607714228548576

def SurrogateDiagonalTailChunk001Sub000Block125Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21671
    = surrogateDiagTailX0RatChunk001Sub000Block125Part022

theorem surrogateDiagonalTailChunk001Sub000Block125Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part022] using hcert

def TailChunk001Sub000Block125Part023SupportExplicit : Finset ℕ :=
  ([21673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block125Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21673
    = surrogateDiagTailX0RatChunk001Sub000Block125Part023

theorem surrogateDiagonalTailChunk001Sub000Block125Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part023] using hcert

def TailChunk001Sub000Block125Part024SupportExplicit : Finset ℕ :=
  ([21674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block125Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block125Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21674
    = surrogateDiagTailX0RatChunk001Sub000Block125Part024

theorem surrogateDiagonalTailChunk001Sub000Block125Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block125Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block125Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block125Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block125Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block125Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block125HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block125Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block125Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block125Part000
    + surrogateDiagTailX0RatChunk001Sub000Block125Part001
    + surrogateDiagTailX0RatChunk001Sub000Block125Part002
    + surrogateDiagTailX0RatChunk001Sub000Block125Part003
    + surrogateDiagTailX0RatChunk001Sub000Block125Part004
    + surrogateDiagTailX0RatChunk001Sub000Block125Part005
    + surrogateDiagTailX0RatChunk001Sub000Block125Part006
    + surrogateDiagTailX0RatChunk001Sub000Block125Part007
    + surrogateDiagTailX0RatChunk001Sub000Block125Part008
    + surrogateDiagTailX0RatChunk001Sub000Block125Part009

def surrogateDiagonalTailChunk001Sub000Block125MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block125Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block125Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block125Part010
    + surrogateDiagTailX0RatChunk001Sub000Block125Part011
    + surrogateDiagTailX0RatChunk001Sub000Block125Part012
    + surrogateDiagTailX0RatChunk001Sub000Block125Part013
    + surrogateDiagTailX0RatChunk001Sub000Block125Part014
    + surrogateDiagTailX0RatChunk001Sub000Block125Part015
    + surrogateDiagTailX0RatChunk001Sub000Block125Part016
    + surrogateDiagTailX0RatChunk001Sub000Block125Part017
    + surrogateDiagTailX0RatChunk001Sub000Block125Part018
    + surrogateDiagTailX0RatChunk001Sub000Block125Part019

def surrogateDiagonalTailChunk001Sub000Block125TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block125Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block125Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block125Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block125Part020
    + surrogateDiagTailX0RatChunk001Sub000Block125Part021
    + surrogateDiagTailX0RatChunk001Sub000Block125Part022
    + surrogateDiagTailX0RatChunk001Sub000Block125Part023
    + surrogateDiagTailX0RatChunk001Sub000Block125Part024

def surrogateDiagonalTailChunk001Sub000Block125Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block125HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block125MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block125TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block125 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block125Part000
    + surrogateDiagTailX0RatChunk001Sub000Block125Part001
    + surrogateDiagTailX0RatChunk001Sub000Block125Part002
    + surrogateDiagTailX0RatChunk001Sub000Block125Part003
    + surrogateDiagTailX0RatChunk001Sub000Block125Part004
    + surrogateDiagTailX0RatChunk001Sub000Block125Part005
    + surrogateDiagTailX0RatChunk001Sub000Block125Part006
    + surrogateDiagTailX0RatChunk001Sub000Block125Part007
    + surrogateDiagTailX0RatChunk001Sub000Block125Part008
    + surrogateDiagTailX0RatChunk001Sub000Block125Part009
    + surrogateDiagTailX0RatChunk001Sub000Block125Part010
    + surrogateDiagTailX0RatChunk001Sub000Block125Part011
    + surrogateDiagTailX0RatChunk001Sub000Block125Part012
    + surrogateDiagTailX0RatChunk001Sub000Block125Part013
    + surrogateDiagTailX0RatChunk001Sub000Block125Part014
    + surrogateDiagTailX0RatChunk001Sub000Block125Part015
    + surrogateDiagTailX0RatChunk001Sub000Block125Part016
    + surrogateDiagTailX0RatChunk001Sub000Block125Part017
    + surrogateDiagTailX0RatChunk001Sub000Block125Part018
    + surrogateDiagTailX0RatChunk001Sub000Block125Part019
    + surrogateDiagTailX0RatChunk001Sub000Block125Part020
    + surrogateDiagTailX0RatChunk001Sub000Block125Part021
    + surrogateDiagTailX0RatChunk001Sub000Block125Part022
    + surrogateDiagTailX0RatChunk001Sub000Block125Part023
    + surrogateDiagTailX0RatChunk001Sub000Block125Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block125_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block125Head + surrogateDiagTailX0RatChunk001Sub000Block125Mid + surrogateDiagTailX0RatChunk001Sub000Block125Tail =
      surrogateDiagTailX0RatChunk001Sub000Block125 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block125Head surrogateDiagTailX0RatChunk001Sub000Block125Mid surrogateDiagTailX0RatChunk001Sub000Block125Tail surrogateDiagTailX0RatChunk001Sub000Block125
  ring

def SurrogateDiagonalTailChunk001Sub000Block125HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block125HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block125Head

def SurrogateDiagonalTailChunk001Sub000Block125MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block125MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block125Mid

def SurrogateDiagonalTailChunk001Sub000Block125TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block125TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block125Tail

theorem surrogateDiagonalTailChunk001Sub000Block125_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block125HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block125MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block125TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block125Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block125 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block125HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block125MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block125TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block125Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block125_eq_head_add_mid_add_tail

/-- Block 126 covers tail-support indices [13150,13175) and q from 21677 to 21715. -/

def TailChunk001Sub000Block126Part000SupportExplicit : Finset ℕ :=
  ([21677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part000 : ℚ :=
  (140931824725 : ℚ) / 506618314600355463168

def SurrogateDiagonalTailChunk001Sub000Block126Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21677
    = surrogateDiagTailX0RatChunk001Sub000Block126Part000

theorem surrogateDiagonalTailChunk001Sub000Block126Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part000] using hcert

def TailChunk001Sub000Block126Part001SupportExplicit : Finset ℕ :=
  ([21678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part001 : ℚ :=
  (7286018725 : ℚ) / 60802268859287424

def SurrogateDiagonalTailChunk001Sub000Block126Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21678
    = surrogateDiagTailX0RatChunk001Sub000Block126Part001

theorem surrogateDiagonalTailChunk001Sub000Block126Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part001] using hcert

def TailChunk001Sub000Block126Part002SupportExplicit : Finset ℕ :=
  ([21679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part002 : ℚ :=
  (686618964575 : ℚ) / 117152603204874200064

def SurrogateDiagonalTailChunk001Sub000Block126Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21679
    = surrogateDiagTailX0RatChunk001Sub000Block126Part002

theorem surrogateDiagonalTailChunk001Sub000Block126Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part002] using hcert

def TailChunk001Sub000Block126Part003SupportExplicit : Finset ℕ :=
  ([21682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part003 : ℚ :=
  (25385511475 : ℚ) / 7633228733351534592

def SurrogateDiagonalTailChunk001Sub000Block126Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21682
    = surrogateDiagTailX0RatChunk001Sub000Block126Part003

theorem surrogateDiagonalTailChunk001Sub000Block126Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part003] using hcert

def TailChunk001Sub000Block126Part004SupportExplicit : Finset ℕ :=
  ([21683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block126Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21683
    = surrogateDiagTailX0RatChunk001Sub000Block126Part004

theorem surrogateDiagonalTailChunk001Sub000Block126Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part004] using hcert

def TailChunk001Sub000Block126Part005SupportExplicit : Finset ℕ :=
  ([21685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part005 : ℚ :=
  (392102215125 : ℚ) / 75422802163391266816

def SurrogateDiagonalTailChunk001Sub000Block126Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21685
    = surrogateDiagTailX0RatChunk001Sub000Block126Part005

theorem surrogateDiagonalTailChunk001Sub000Block126Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part005] using hcert

def TailChunk001Sub000Block126Part006SupportExplicit : Finset ℕ :=
  ([21686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part006 : ℚ :=
  (600590961925 : ℚ) / 18608685060561389568

def SurrogateDiagonalTailChunk001Sub000Block126Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21686
    = surrogateDiagTailX0RatChunk001Sub000Block126Part006

theorem surrogateDiagonalTailChunk001Sub000Block126Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part006] using hcert

def TailChunk001Sub000Block126Part007SupportExplicit : Finset ℕ :=
  ([21687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part007 : ℚ :=
  (125025 : ℚ) / 21835470913538048

def SurrogateDiagonalTailChunk001Sub000Block126Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21687
    = surrogateDiagTailX0RatChunk001Sub000Block126Part007

theorem surrogateDiagonalTailChunk001Sub000Block126Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part007] using hcert

def TailChunk001Sub000Block126Part008SupportExplicit : Finset ℕ :=
  ([21691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part008 : ℚ :=
  (94806392875 : ℚ) / 522856657071349843968

def SurrogateDiagonalTailChunk001Sub000Block126Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21691
    = surrogateDiagTailX0RatChunk001Sub000Block126Part008

theorem surrogateDiagonalTailChunk001Sub000Block126Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part008] using hcert

def TailChunk001Sub000Block126Part009SupportExplicit : Finset ℕ :=
  ([21693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part009 : ℚ :=
  (469777038175 : ℚ) / 58812634265477971968

def SurrogateDiagonalTailChunk001Sub000Block126Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21693
    = surrogateDiagTailX0RatChunk001Sub000Block126Part009

theorem surrogateDiagonalTailChunk001Sub000Block126Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part009] using hcert

def TailChunk001Sub000Block126Part010SupportExplicit : Finset ℕ :=
  ([21694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block126Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21694
    = surrogateDiagTailX0RatChunk001Sub000Block126Part010

theorem surrogateDiagonalTailChunk001Sub000Block126Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part010] using hcert

def TailChunk001Sub000Block126Part011SupportExplicit : Finset ℕ :=
  ([21695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part011 : ℚ :=
  (1177390895125 : ℚ) / 226686164803190212608

def SurrogateDiagonalTailChunk001Sub000Block126Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21695
    = surrogateDiagTailX0RatChunk001Sub000Block126Part011

theorem surrogateDiagonalTailChunk001Sub000Block126Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part011] using hcert

def TailChunk001Sub000Block126Part012SupportExplicit : Finset ℕ :=
  ([21697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part012 : ℚ :=
  (262605760025 : ℚ) / 200680896563363856384

def SurrogateDiagonalTailChunk001Sub000Block126Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21697
    = surrogateDiagTailX0RatChunk001Sub000Block126Part012

theorem surrogateDiagonalTailChunk001Sub000Block126Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part012] using hcert

def TailChunk001Sub000Block126Part013SupportExplicit : Finset ℕ :=
  ([21698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part013 : ℚ :=
  (58776761 : ℚ) / 8658971768189025

def SurrogateDiagonalTailChunk001Sub000Block126Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21698
    = surrogateDiagTailX0RatChunk001Sub000Block126Part013

theorem surrogateDiagonalTailChunk001Sub000Block126Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part013] using hcert

def TailChunk001Sub000Block126Part014SupportExplicit : Finset ℕ :=
  ([21701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block126Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21701
    = surrogateDiagTailX0RatChunk001Sub000Block126Part014

theorem surrogateDiagonalTailChunk001Sub000Block126Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part014] using hcert

def TailChunk001Sub000Block126Part015SupportExplicit : Finset ℕ :=
  ([21702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part015 : ℚ :=
  (204460274275 : ℚ) / 1710017431178575872

def SurrogateDiagonalTailChunk001Sub000Block126Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21702
    = surrogateDiagTailX0RatChunk001Sub000Block126Part015

theorem surrogateDiagonalTailChunk001Sub000Block126Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part015] using hcert

def TailChunk001Sub000Block126Part016SupportExplicit : Finset ℕ :=
  ([21703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part016 : ℚ :=
  (4891285639 : ℚ) / 3781416381713932800

def SurrogateDiagonalTailChunk001Sub000Block126Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21703
    = surrogateDiagTailX0RatChunk001Sub000Block126Part016

theorem surrogateDiagonalTailChunk001Sub000Block126Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part016] using hcert

def TailChunk001Sub000Block126Part017SupportExplicit : Finset ℕ :=
  ([21705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part017 : ℚ :=
  (98343820925 : ℚ) / 5597189254399758336

def SurrogateDiagonalTailChunk001Sub000Block126Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21705
    = surrogateDiagTailX0RatChunk001Sub000Block126Part017

theorem surrogateDiagonalTailChunk001Sub000Block126Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part017] using hcert

def TailChunk001Sub000Block126Part018SupportExplicit : Finset ℕ :=
  ([21706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block126Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21706
    = surrogateDiagTailX0RatChunk001Sub000Block126Part018

theorem surrogateDiagonalTailChunk001Sub000Block126Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part018] using hcert

def TailChunk001Sub000Block126Part019SupportExplicit : Finset ℕ :=
  ([21709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part019 : ℚ :=
  (3403294075 : ℚ) / 3590245253652676608

def SurrogateDiagonalTailChunk001Sub000Block126Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21709
    = surrogateDiagTailX0RatChunk001Sub000Block126Part019

theorem surrogateDiagonalTailChunk001Sub000Block126Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part019] using hcert

def TailChunk001Sub000Block126Part020SupportExplicit : Finset ℕ :=
  ([21710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part020 : ℚ :=
  (712389499825 : ℚ) / 10079155849265676288

def SurrogateDiagonalTailChunk001Sub000Block126Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21710
    = surrogateDiagTailX0RatChunk001Sub000Block126Part020

theorem surrogateDiagonalTailChunk001Sub000Block126Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part020] using hcert

def TailChunk001Sub000Block126Part021SupportExplicit : Finset ℕ :=
  ([21711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part021 : ℚ :=
  (41675 : ℚ) / 7310767373899776

def SurrogateDiagonalTailChunk001Sub000Block126Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21711
    = surrogateDiagTailX0RatChunk001Sub000Block126Part021

theorem surrogateDiagonalTailChunk001Sub000Block126Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part021] using hcert

def TailChunk001Sub000Block126Part022SupportExplicit : Finset ℕ :=
  ([21713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block126Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21713
    = surrogateDiagTailX0RatChunk001Sub000Block126Part022

theorem surrogateDiagonalTailChunk001Sub000Block126Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part022] using hcert

def TailChunk001Sub000Block126Part023SupportExplicit : Finset ℕ :=
  ([21714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part023 : ℚ :=
  (1330425383 : ℚ) / 3439373945241600

def SurrogateDiagonalTailChunk001Sub000Block126Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21714
    = surrogateDiagTailX0RatChunk001Sub000Block126Part023

theorem surrogateDiagonalTailChunk001Sub000Block126Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part023] using hcert

def TailChunk001Sub000Block126Part024SupportExplicit : Finset ℕ :=
  ([21715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block126Part024 : ℚ :=
  (2046303391 : ℚ) / 318701397934080000

def SurrogateDiagonalTailChunk001Sub000Block126Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21715
    = surrogateDiagTailX0RatChunk001Sub000Block126Part024

theorem surrogateDiagonalTailChunk001Sub000Block126Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block126Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block126Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block126Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block126Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block126Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block126HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block126Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block126Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block126Part000
    + surrogateDiagTailX0RatChunk001Sub000Block126Part001
    + surrogateDiagTailX0RatChunk001Sub000Block126Part002
    + surrogateDiagTailX0RatChunk001Sub000Block126Part003
    + surrogateDiagTailX0RatChunk001Sub000Block126Part004
    + surrogateDiagTailX0RatChunk001Sub000Block126Part005
    + surrogateDiagTailX0RatChunk001Sub000Block126Part006
    + surrogateDiagTailX0RatChunk001Sub000Block126Part007
    + surrogateDiagTailX0RatChunk001Sub000Block126Part008
    + surrogateDiagTailX0RatChunk001Sub000Block126Part009

def surrogateDiagonalTailChunk001Sub000Block126MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block126Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block126Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block126Part010
    + surrogateDiagTailX0RatChunk001Sub000Block126Part011
    + surrogateDiagTailX0RatChunk001Sub000Block126Part012
    + surrogateDiagTailX0RatChunk001Sub000Block126Part013
    + surrogateDiagTailX0RatChunk001Sub000Block126Part014
    + surrogateDiagTailX0RatChunk001Sub000Block126Part015
    + surrogateDiagTailX0RatChunk001Sub000Block126Part016
    + surrogateDiagTailX0RatChunk001Sub000Block126Part017
    + surrogateDiagTailX0RatChunk001Sub000Block126Part018
    + surrogateDiagTailX0RatChunk001Sub000Block126Part019

def surrogateDiagonalTailChunk001Sub000Block126TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block126Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block126Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block126Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block126Part020
    + surrogateDiagTailX0RatChunk001Sub000Block126Part021
    + surrogateDiagTailX0RatChunk001Sub000Block126Part022
    + surrogateDiagTailX0RatChunk001Sub000Block126Part023
    + surrogateDiagTailX0RatChunk001Sub000Block126Part024

def surrogateDiagonalTailChunk001Sub000Block126Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block126HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block126MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block126TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block126 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block126Part000
    + surrogateDiagTailX0RatChunk001Sub000Block126Part001
    + surrogateDiagTailX0RatChunk001Sub000Block126Part002
    + surrogateDiagTailX0RatChunk001Sub000Block126Part003
    + surrogateDiagTailX0RatChunk001Sub000Block126Part004
    + surrogateDiagTailX0RatChunk001Sub000Block126Part005
    + surrogateDiagTailX0RatChunk001Sub000Block126Part006
    + surrogateDiagTailX0RatChunk001Sub000Block126Part007
    + surrogateDiagTailX0RatChunk001Sub000Block126Part008
    + surrogateDiagTailX0RatChunk001Sub000Block126Part009
    + surrogateDiagTailX0RatChunk001Sub000Block126Part010
    + surrogateDiagTailX0RatChunk001Sub000Block126Part011
    + surrogateDiagTailX0RatChunk001Sub000Block126Part012
    + surrogateDiagTailX0RatChunk001Sub000Block126Part013
    + surrogateDiagTailX0RatChunk001Sub000Block126Part014
    + surrogateDiagTailX0RatChunk001Sub000Block126Part015
    + surrogateDiagTailX0RatChunk001Sub000Block126Part016
    + surrogateDiagTailX0RatChunk001Sub000Block126Part017
    + surrogateDiagTailX0RatChunk001Sub000Block126Part018
    + surrogateDiagTailX0RatChunk001Sub000Block126Part019
    + surrogateDiagTailX0RatChunk001Sub000Block126Part020
    + surrogateDiagTailX0RatChunk001Sub000Block126Part021
    + surrogateDiagTailX0RatChunk001Sub000Block126Part022
    + surrogateDiagTailX0RatChunk001Sub000Block126Part023
    + surrogateDiagTailX0RatChunk001Sub000Block126Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block126_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block126Head + surrogateDiagTailX0RatChunk001Sub000Block126Mid + surrogateDiagTailX0RatChunk001Sub000Block126Tail =
      surrogateDiagTailX0RatChunk001Sub000Block126 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block126Head surrogateDiagTailX0RatChunk001Sub000Block126Mid surrogateDiagTailX0RatChunk001Sub000Block126Tail surrogateDiagTailX0RatChunk001Sub000Block126
  ring

def SurrogateDiagonalTailChunk001Sub000Block126HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block126HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block126Head

def SurrogateDiagonalTailChunk001Sub000Block126MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block126MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block126Mid

def SurrogateDiagonalTailChunk001Sub000Block126TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block126TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block126Tail

theorem surrogateDiagonalTailChunk001Sub000Block126_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block126HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block126MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block126TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block126Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block126 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block126HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block126MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block126TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block126Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block126_eq_head_add_mid_add_tail

/-- Block 127 covers tail-support indices [13175,13200) and q from 21718 to 21757. -/

def TailChunk001Sub000Block127Part000SupportExplicit : Finset ℕ :=
  ([21718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block127Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21718
    = surrogateDiagTailX0RatChunk001Sub000Block127Part000

theorem surrogateDiagonalTailChunk001Sub000Block127Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part000] using hcert

def TailChunk001Sub000Block127Part001SupportExplicit : Finset ℕ :=
  ([21719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part001 : ℚ :=
  (3779474225 : ℚ) / 9171356309053074432

def SurrogateDiagonalTailChunk001Sub000Block127Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21719
    = surrogateDiagTailX0RatChunk001Sub000Block127Part001

theorem surrogateDiagonalTailChunk001Sub000Block127Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part001] using hcert

def TailChunk001Sub000Block127Part002SupportExplicit : Finset ℕ :=
  ([21721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part002 : ℚ :=
  (6399076825 : ℚ) / 1995799464343093248

def SurrogateDiagonalTailChunk001Sub000Block127Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21721
    = surrogateDiagTailX0RatChunk001Sub000Block127Part002

theorem surrogateDiagonalTailChunk001Sub000Block127Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part002] using hcert

def TailChunk001Sub000Block127Part003SupportExplicit : Finset ℕ :=
  ([21722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block127Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21722
    = surrogateDiagTailX0RatChunk001Sub000Block127Part003

theorem surrogateDiagonalTailChunk001Sub000Block127Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part003] using hcert

def TailChunk001Sub000Block127Part004SupportExplicit : Finset ℕ :=
  ([21723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part004 : ℚ :=
  (355345990375 : ℚ) / 79281341852193128448

def SurrogateDiagonalTailChunk001Sub000Block127Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21723
    = surrogateDiagTailX0RatChunk001Sub000Block127Part004

theorem surrogateDiagonalTailChunk001Sub000Block127Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part004] using hcert

def TailChunk001Sub000Block127Part005SupportExplicit : Finset ℕ :=
  ([21727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block127Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21727
    = surrogateDiagTailX0RatChunk001Sub000Block127Part005

theorem surrogateDiagonalTailChunk001Sub000Block127Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part005] using hcert

def TailChunk001Sub000Block127Part006SupportExplicit : Finset ℕ :=
  ([21729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part006 : ℚ :=
  (41675 : ℚ) / 7335045534416256

def SurrogateDiagonalTailChunk001Sub000Block127Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21729
    = surrogateDiagTailX0RatChunk001Sub000Block127Part006

theorem surrogateDiagonalTailChunk001Sub000Block127Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part006] using hcert

def TailChunk001Sub000Block127Part007SupportExplicit : Finset ℕ :=
  ([21730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part007 : ℚ :=
  (4358554539 : ℚ) / 79878316831539200

def SurrogateDiagonalTailChunk001Sub000Block127Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21730
    = surrogateDiagTailX0RatChunk001Sub000Block127Part007

theorem surrogateDiagonalTailChunk001Sub000Block127Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part007] using hcert

def TailChunk001Sub000Block127Part008SupportExplicit : Finset ℕ :=
  ([21731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part008 : ℚ :=
  (638509433 : ℚ) / 1389427830000000000

def SurrogateDiagonalTailChunk001Sub000Block127Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21731
    = surrogateDiagTailX0RatChunk001Sub000Block127Part008

theorem surrogateDiagonalTailChunk001Sub000Block127Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part008] using hcert

def TailChunk001Sub000Block127Part009SupportExplicit : Finset ℕ :=
  ([21733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part009 : ℚ :=
  (5152181 : ℚ) / 27851136429463200

def SurrogateDiagonalTailChunk001Sub000Block127Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21733
    = surrogateDiagTailX0RatChunk001Sub000Block127Part009

theorem surrogateDiagonalTailChunk001Sub000Block127Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part009] using hcert

def TailChunk001Sub000Block127Part010SupportExplicit : Finset ℕ :=
  ([21734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block127Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21734
    = surrogateDiagTailX0RatChunk001Sub000Block127Part010

theorem surrogateDiagonalTailChunk001Sub000Block127Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part010] using hcert

def TailChunk001Sub000Block127Part011SupportExplicit : Finset ℕ :=
  ([21737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block127Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21737
    = surrogateDiagTailX0RatChunk001Sub000Block127Part011

theorem surrogateDiagonalTailChunk001Sub000Block127Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part011] using hcert

def TailChunk001Sub000Block127Part012SupportExplicit : Finset ℕ :=
  ([21738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part012 : ℚ :=
  (410277673475 : ℚ) / 3442790768578741824

def SurrogateDiagonalTailChunk001Sub000Block127Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21738
    = surrogateDiagTailX0RatChunk001Sub000Block127Part012

theorem surrogateDiagonalTailChunk001Sub000Block127Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part012] using hcert

def TailChunk001Sub000Block127Part013SupportExplicit : Finset ℕ :=
  ([21739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block127Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21739
    = surrogateDiagTailX0RatChunk001Sub000Block127Part013

theorem surrogateDiagonalTailChunk001Sub000Block127Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part013] using hcert

def TailChunk001Sub000Block127Part014SupportExplicit : Finset ℕ :=
  ([21741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part014 : ℚ :=
  (13126753275325 : ℚ) / 110291021809373394048

def SurrogateDiagonalTailChunk001Sub000Block127Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21741
    = surrogateDiagTailX0RatChunk001Sub000Block127Part014

theorem surrogateDiagonalTailChunk001Sub000Block127Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part014] using hcert

def TailChunk001Sub000Block127Part015SupportExplicit : Finset ℕ :=
  ([21742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part015 : ℚ :=
  (326332829975 : ℚ) / 1044542759509426176

def SurrogateDiagonalTailChunk001Sub000Block127Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21742
    = surrogateDiagTailX0RatChunk001Sub000Block127Part015

theorem surrogateDiagonalTailChunk001Sub000Block127Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part015] using hcert

def TailChunk001Sub000Block127Part016SupportExplicit : Finset ℕ :=
  ([21743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part016 : ℚ :=
  (6611399635525 : ℚ) / 109287430061298941952

def SurrogateDiagonalTailChunk001Sub000Block127Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21743
    = surrogateDiagTailX0RatChunk001Sub000Block127Part016

theorem surrogateDiagonalTailChunk001Sub000Block127Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part016] using hcert

def TailChunk001Sub000Block127Part017SupportExplicit : Finset ℕ :=
  ([21745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part017 : ℚ :=
  (20089814023975 : ℚ) / 228783640219050344448

def SurrogateDiagonalTailChunk001Sub000Block127Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21745
    = surrogateDiagTailX0RatChunk001Sub000Block127Part017

theorem surrogateDiagonalTailChunk001Sub000Block127Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part017] using hcert

def TailChunk001Sub000Block127Part018SupportExplicit : Finset ℕ :=
  ([21746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part018 : ℚ :=
  (23891344311 : ℚ) / 107630268310645600

def SurrogateDiagonalTailChunk001Sub000Block127Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21746
    = surrogateDiagTailX0RatChunk001Sub000Block127Part018

theorem surrogateDiagonalTailChunk001Sub000Block127Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part018] using hcert

def TailChunk001Sub000Block127Part019SupportExplicit : Finset ℕ :=
  ([21747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part019 : ℚ :=
  (447278625163 : ℚ) / 2999925069776947200

def SurrogateDiagonalTailChunk001Sub000Block127Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21747
    = surrogateDiagTailX0RatChunk001Sub000Block127Part019

theorem surrogateDiagonalTailChunk001Sub000Block127Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part019] using hcert

def TailChunk001Sub000Block127Part020SupportExplicit : Finset ℕ :=
  ([21749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part020 : ℚ :=
  (4799272837375 : ℚ) / 53901975400125898752

def SurrogateDiagonalTailChunk001Sub000Block127Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21749
    = surrogateDiagTailX0RatChunk001Sub000Block127Part020

theorem surrogateDiagonalTailChunk001Sub000Block127Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part020] using hcert

def TailChunk001Sub000Block127Part021SupportExplicit : Finset ℕ :=
  ([21751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part021 : ℚ :=
  (473106001 : ℚ) / 8953315461281250

def SurrogateDiagonalTailChunk001Sub000Block127Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21751
    = surrogateDiagTailX0RatChunk001Sub000Block127Part021

theorem surrogateDiagonalTailChunk001Sub000Block127Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part021] using hcert

def TailChunk001Sub000Block127Part022SupportExplicit : Finset ℕ :=
  ([21754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part022 : ℚ :=
  (3582546289325 : ℚ) / 16120321926842548224

def SurrogateDiagonalTailChunk001Sub000Block127Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21754
    = surrogateDiagTailX0RatChunk001Sub000Block127Part022

theorem surrogateDiagonalTailChunk001Sub000Block127Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part022] using hcert

def TailChunk001Sub000Block127Part023SupportExplicit : Finset ℕ :=
  ([21755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part023 : ℚ :=
  (9089537203625 : ℚ) / 90795899808005750784

def SurrogateDiagonalTailChunk001Sub000Block127Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21755
    = surrogateDiagTailX0RatChunk001Sub000Block127Part023

theorem surrogateDiagonalTailChunk001Sub000Block127Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part023] using hcert

def TailChunk001Sub000Block127Part024SupportExplicit : Finset ℕ :=
  ([21757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block127Part024 : ℚ :=
  (7396360140625 : ℚ) / 140049985478431002912

def SurrogateDiagonalTailChunk001Sub000Block127Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21757
    = surrogateDiagTailX0RatChunk001Sub000Block127Part024

theorem surrogateDiagonalTailChunk001Sub000Block127Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block127Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block127Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block127Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block127Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block127Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block127HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block127Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block127Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block127Part000
    + surrogateDiagTailX0RatChunk001Sub000Block127Part001
    + surrogateDiagTailX0RatChunk001Sub000Block127Part002
    + surrogateDiagTailX0RatChunk001Sub000Block127Part003
    + surrogateDiagTailX0RatChunk001Sub000Block127Part004
    + surrogateDiagTailX0RatChunk001Sub000Block127Part005
    + surrogateDiagTailX0RatChunk001Sub000Block127Part006
    + surrogateDiagTailX0RatChunk001Sub000Block127Part007
    + surrogateDiagTailX0RatChunk001Sub000Block127Part008
    + surrogateDiagTailX0RatChunk001Sub000Block127Part009

def surrogateDiagonalTailChunk001Sub000Block127MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block127Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block127Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block127Part010
    + surrogateDiagTailX0RatChunk001Sub000Block127Part011
    + surrogateDiagTailX0RatChunk001Sub000Block127Part012
    + surrogateDiagTailX0RatChunk001Sub000Block127Part013
    + surrogateDiagTailX0RatChunk001Sub000Block127Part014
    + surrogateDiagTailX0RatChunk001Sub000Block127Part015
    + surrogateDiagTailX0RatChunk001Sub000Block127Part016
    + surrogateDiagTailX0RatChunk001Sub000Block127Part017
    + surrogateDiagTailX0RatChunk001Sub000Block127Part018
    + surrogateDiagTailX0RatChunk001Sub000Block127Part019

def surrogateDiagonalTailChunk001Sub000Block127TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block127Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block127Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block127Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block127Part020
    + surrogateDiagTailX0RatChunk001Sub000Block127Part021
    + surrogateDiagTailX0RatChunk001Sub000Block127Part022
    + surrogateDiagTailX0RatChunk001Sub000Block127Part023
    + surrogateDiagTailX0RatChunk001Sub000Block127Part024

def surrogateDiagonalTailChunk001Sub000Block127Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block127HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block127MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block127TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block127 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block127Part000
    + surrogateDiagTailX0RatChunk001Sub000Block127Part001
    + surrogateDiagTailX0RatChunk001Sub000Block127Part002
    + surrogateDiagTailX0RatChunk001Sub000Block127Part003
    + surrogateDiagTailX0RatChunk001Sub000Block127Part004
    + surrogateDiagTailX0RatChunk001Sub000Block127Part005
    + surrogateDiagTailX0RatChunk001Sub000Block127Part006
    + surrogateDiagTailX0RatChunk001Sub000Block127Part007
    + surrogateDiagTailX0RatChunk001Sub000Block127Part008
    + surrogateDiagTailX0RatChunk001Sub000Block127Part009
    + surrogateDiagTailX0RatChunk001Sub000Block127Part010
    + surrogateDiagTailX0RatChunk001Sub000Block127Part011
    + surrogateDiagTailX0RatChunk001Sub000Block127Part012
    + surrogateDiagTailX0RatChunk001Sub000Block127Part013
    + surrogateDiagTailX0RatChunk001Sub000Block127Part014
    + surrogateDiagTailX0RatChunk001Sub000Block127Part015
    + surrogateDiagTailX0RatChunk001Sub000Block127Part016
    + surrogateDiagTailX0RatChunk001Sub000Block127Part017
    + surrogateDiagTailX0RatChunk001Sub000Block127Part018
    + surrogateDiagTailX0RatChunk001Sub000Block127Part019
    + surrogateDiagTailX0RatChunk001Sub000Block127Part020
    + surrogateDiagTailX0RatChunk001Sub000Block127Part021
    + surrogateDiagTailX0RatChunk001Sub000Block127Part022
    + surrogateDiagTailX0RatChunk001Sub000Block127Part023
    + surrogateDiagTailX0RatChunk001Sub000Block127Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block127_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block127Head + surrogateDiagTailX0RatChunk001Sub000Block127Mid + surrogateDiagTailX0RatChunk001Sub000Block127Tail =
      surrogateDiagTailX0RatChunk001Sub000Block127 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block127Head surrogateDiagTailX0RatChunk001Sub000Block127Mid surrogateDiagTailX0RatChunk001Sub000Block127Tail surrogateDiagTailX0RatChunk001Sub000Block127
  ring

def SurrogateDiagonalTailChunk001Sub000Block127HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block127HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block127Head

def SurrogateDiagonalTailChunk001Sub000Block127MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block127MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block127Mid

def SurrogateDiagonalTailChunk001Sub000Block127TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block127TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block127Tail

theorem surrogateDiagonalTailChunk001Sub000Block127_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block127HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block127MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block127TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block127Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block127 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block127HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block127MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block127TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block127Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block127_eq_head_add_mid_add_tail

/-- Block 128 covers tail-support indices [13200,13225) and q from 21758 to 21795. -/

def TailChunk001Sub000Block128Part000SupportExplicit : Finset ℕ :=
  ([21758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part000 : ℚ :=
  (229081411477 : ℚ) / 729079244867635200

def SurrogateDiagonalTailChunk001Sub000Block128Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21758
    = surrogateDiagTailX0RatChunk001Sub000Block128Part000

theorem surrogateDiagonalTailChunk001Sub000Block128Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part000] using hcert

def TailChunk001Sub000Block128Part001SupportExplicit : Finset ℕ :=
  ([21759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part001 : ℚ :=
  (13148500274725 : ℚ) / 110656778649624496128

def SurrogateDiagonalTailChunk001Sub000Block128Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21759
    = surrogateDiagTailX0RatChunk001Sub000Block128Part001

theorem surrogateDiagonalTailChunk001Sub000Block128Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part001] using hcert

def TailChunk001Sub000Block128Part002SupportExplicit : Finset ℕ :=
  ([21761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part002 : ℚ :=
  (7094439368875 : ℚ) / 127516415601877438752

def SurrogateDiagonalTailChunk001Sub000Block128Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21761
    = surrogateDiagTailX0RatChunk001Sub000Block128Part002

theorem surrogateDiagonalTailChunk001Sub000Block128Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part002] using hcert

def TailChunk001Sub000Block128Part003SupportExplicit : Finset ℕ :=
  ([21763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part003 : ℚ :=
  (22341291340225 : ℚ) / 302381976143351236608

def SurrogateDiagonalTailChunk001Sub000Block128Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21763
    = surrogateDiagTailX0RatChunk001Sub000Block128Part003

theorem surrogateDiagonalTailChunk001Sub000Block128Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part003] using hcert

def TailChunk001Sub000Block128Part004SupportExplicit : Finset ℕ :=
  ([21765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part004 : ℚ :=
  (46005431063 : ℚ) / 226375185984000000

def SurrogateDiagonalTailChunk001Sub000Block128Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21765
    = surrogateDiagTailX0RatChunk001Sub000Block128Part004

theorem surrogateDiagonalTailChunk001Sub000Block128Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part004] using hcert

def TailChunk001Sub000Block128Part005SupportExplicit : Finset ℕ :=
  ([21766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part005 : ℚ :=
  (1850620140625 : ℚ) / 8766005803384168722

def SurrogateDiagonalTailChunk001Sub000Block128Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21766
    = surrogateDiagTailX0RatChunk001Sub000Block128Part005

theorem surrogateDiagonalTailChunk001Sub000Block128Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part005] using hcert

def TailChunk001Sub000Block128Part006SupportExplicit : Finset ℕ :=
  ([21767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part006 : ℚ :=
  (7403160765625 : ℚ) / 140307655224028043442

def SurrogateDiagonalTailChunk001Sub000Block128Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21767
    = surrogateDiagTailX0RatChunk001Sub000Block128Part006

theorem surrogateDiagonalTailChunk001Sub000Block128Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part006] using hcert

def TailChunk001Sub000Block128Part007SupportExplicit : Finset ℕ :=
  ([21769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part007 : ℚ :=
  (20789220393 : ℚ) / 318970678259709400

def SurrogateDiagonalTailChunk001Sub000Block128Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21769
    = surrogateDiagTailX0RatChunk001Sub000Block128Part007

theorem surrogateDiagonalTailChunk001Sub000Block128Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part007] using hcert

def TailChunk001Sub000Block128Part008SupportExplicit : Finset ℕ :=
  ([21770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part008 : ℚ :=
  (39477689263 : ℚ) / 76615845929164800

def SurrogateDiagonalTailChunk001Sub000Block128Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21770
    = surrogateDiagTailX0RatChunk001Sub000Block128Part008

theorem surrogateDiagonalTailChunk001Sub000Block128Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part008] using hcert

def TailChunk001Sub000Block128Part009SupportExplicit : Finset ℕ :=
  ([21773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part009 : ℚ :=
  (7407242640625 : ℚ) / 140462427637754080032

def SurrogateDiagonalTailChunk001Sub000Block128Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21773
    = surrogateDiagTailX0RatChunk001Sub000Block128Part009

theorem surrogateDiagonalTailChunk001Sub000Block128Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part009] using hcert

def TailChunk001Sub000Block128Part010SupportExplicit : Finset ℕ :=
  ([21774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part010 : ℚ :=
  (151007739397 : ℚ) / 218933014583347200

def SurrogateDiagonalTailChunk001Sub000Block128Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21774
    = surrogateDiagTailX0RatChunk001Sub000Block128Part010

theorem surrogateDiagonalTailChunk001Sub000Block128Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part010] using hcert

def TailChunk001Sub000Block128Part011SupportExplicit : Finset ℕ :=
  ([21777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part011 : ℚ :=
  (17778618437 : ℚ) / 88077863391068160

def SurrogateDiagonalTailChunk001Sub000Block128Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21777
    = surrogateDiagTailX0RatChunk001Sub000Block128Part011

theorem surrogateDiagonalTailChunk001Sub000Block128Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part011] using hcert

def TailChunk001Sub000Block128Part012SupportExplicit : Finset ℕ :=
  ([21778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part012 : ℚ :=
  (1852661265625 : ℚ) / 8785355022485524992

def SurrogateDiagonalTailChunk001Sub000Block128Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21778
    = surrogateDiagTailX0RatChunk001Sub000Block128Part012

theorem surrogateDiagonalTailChunk001Sub000Block128Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part012] using hcert

def TailChunk001Sub000Block128Part013SupportExplicit : Finset ℕ :=
  ([21779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part013 : ℚ :=
  (1111370271331 : ℚ) / 19451989620000000000

def SurrogateDiagonalTailChunk001Sub000Block128Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21779
    = surrogateDiagTailX0RatChunk001Sub000Block128Part013

theorem surrogateDiagonalTailChunk001Sub000Block128Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part013] using hcert

def TailChunk001Sub000Block128Part014SupportExplicit : Finset ℕ :=
  ([21781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part014 : ℚ :=
  (27359930729575 : ℚ) / 469118033147536215168

def SurrogateDiagonalTailChunk001Sub000Block128Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21781
    = surrogateDiagTailX0RatChunk001Sub000Block128Part014

theorem surrogateDiagonalTailChunk001Sub000Block128Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part014] using hcert

def TailChunk001Sub000Block128Part015SupportExplicit : Finset ℕ :=
  ([21782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part015 : ℚ :=
  (2965347025 : ℚ) / 14066898999646482

def SurrogateDiagonalTailChunk001Sub000Block128Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21782
    = surrogateDiagTailX0RatChunk001Sub000Block128Part015

theorem surrogateDiagonalTailChunk001Sub000Block128Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part015] using hcert

def TailChunk001Sub000Block128Part016SupportExplicit : Finset ℕ :=
  ([21783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part016 : ℚ :=
  (12615128238925 : ℚ) / 100072753501304782848

def SurrogateDiagonalTailChunk001Sub000Block128Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21783
    = surrogateDiagTailX0RatChunk001Sub000Block128Part016

theorem surrogateDiagonalTailChunk001Sub000Block128Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part016] using hcert

def TailChunk001Sub000Block128Part017SupportExplicit : Finset ℕ :=
  ([21785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part017 : ℚ :=
  (395333046875 : ℚ) / 4801501525212665856

def SurrogateDiagonalTailChunk001Sub000Block128Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21785
    = surrogateDiagTailX0RatChunk001Sub000Block128Part017

theorem surrogateDiagonalTailChunk001Sub000Block128Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part017] using hcert

def TailChunk001Sub000Block128Part018SupportExplicit : Finset ℕ :=
  ([21786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part018 : ℚ :=
  (41190649417 : ℚ) / 69466167899488800

def SurrogateDiagonalTailChunk001Sub000Block128Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21786
    = surrogateDiagTailX0RatChunk001Sub000Block128Part018

theorem surrogateDiagonalTailChunk001Sub000Block128Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part018] using hcert

def TailChunk001Sub000Block128Part019SupportExplicit : Finset ℕ :=
  ([21787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part019 : ℚ :=
  (7416771390625 : ℚ) / 140824061212282385202

def SurrogateDiagonalTailChunk001Sub000Block128Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21787
    = surrogateDiagTailX0RatChunk001Sub000Block128Part019

theorem surrogateDiagonalTailChunk001Sub000Block128Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part019] using hcert

def TailChunk001Sub000Block128Part020SupportExplicit : Finset ℕ :=
  ([21790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part020 : ℚ :=
  (5041888969225 : ℚ) / 14404504575637997568

def SurrogateDiagonalTailChunk001Sub000Block128Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21790
    = surrogateDiagTailX0RatChunk001Sub000Block128Part020

theorem surrogateDiagonalTailChunk001Sub000Block128Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part020] using hcert

def TailChunk001Sub000Block128Part021SupportExplicit : Finset ℕ :=
  ([21791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part021 : ℚ :=
  (746487535699 : ℚ) / 8197629480552499200

def SurrogateDiagonalTailChunk001Sub000Block128Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21791
    = surrogateDiagTailX0RatChunk001Sub000Block128Part021

theorem surrogateDiagonalTailChunk001Sub000Block128Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part021] using hcert

def TailChunk001Sub000Block128Part022SupportExplicit : Finset ℕ :=
  ([21793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part022 : ℚ :=
  (969594155509 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub000Block128Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21793
    = surrogateDiagTailX0RatChunk001Sub000Block128Part022

theorem surrogateDiagonalTailChunk001Sub000Block128Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part022] using hcert

def TailChunk001Sub000Block128Part023SupportExplicit : Finset ℕ :=
  ([21794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part023 : ℚ :=
  (26852040667 : ℚ) / 109973153010155520

def SurrogateDiagonalTailChunk001Sub000Block128Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21794
    = surrogateDiagTailX0RatChunk001Sub000Block128Part023

theorem surrogateDiagonalTailChunk001Sub000Block128Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part023] using hcert

def TailChunk001Sub000Block128Part024SupportExplicit : Finset ℕ :=
  ([21795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block128Part024 : ℚ :=
  (1087293400625 : ℚ) / 5690668474326122496

def SurrogateDiagonalTailChunk001Sub000Block128Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21795
    = surrogateDiagTailX0RatChunk001Sub000Block128Part024

theorem surrogateDiagonalTailChunk001Sub000Block128Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block128Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block128Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block128Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block128Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block128Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block128Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block128HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block128Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block128Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block128Part000
    + surrogateDiagTailX0RatChunk001Sub000Block128Part001
    + surrogateDiagTailX0RatChunk001Sub000Block128Part002
    + surrogateDiagTailX0RatChunk001Sub000Block128Part003
    + surrogateDiagTailX0RatChunk001Sub000Block128Part004
    + surrogateDiagTailX0RatChunk001Sub000Block128Part005
    + surrogateDiagTailX0RatChunk001Sub000Block128Part006
    + surrogateDiagTailX0RatChunk001Sub000Block128Part007
    + surrogateDiagTailX0RatChunk001Sub000Block128Part008
    + surrogateDiagTailX0RatChunk001Sub000Block128Part009

def surrogateDiagonalTailChunk001Sub000Block128MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block128Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block128Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block128Part010
    + surrogateDiagTailX0RatChunk001Sub000Block128Part011
    + surrogateDiagTailX0RatChunk001Sub000Block128Part012
    + surrogateDiagTailX0RatChunk001Sub000Block128Part013
    + surrogateDiagTailX0RatChunk001Sub000Block128Part014
    + surrogateDiagTailX0RatChunk001Sub000Block128Part015
    + surrogateDiagTailX0RatChunk001Sub000Block128Part016
    + surrogateDiagTailX0RatChunk001Sub000Block128Part017
    + surrogateDiagTailX0RatChunk001Sub000Block128Part018
    + surrogateDiagTailX0RatChunk001Sub000Block128Part019

def surrogateDiagonalTailChunk001Sub000Block128TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block128Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block128Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block128Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block128Part020
    + surrogateDiagTailX0RatChunk001Sub000Block128Part021
    + surrogateDiagTailX0RatChunk001Sub000Block128Part022
    + surrogateDiagTailX0RatChunk001Sub000Block128Part023
    + surrogateDiagTailX0RatChunk001Sub000Block128Part024

def surrogateDiagonalTailChunk001Sub000Block128Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block128HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block128MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block128TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block128 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block128Part000
    + surrogateDiagTailX0RatChunk001Sub000Block128Part001
    + surrogateDiagTailX0RatChunk001Sub000Block128Part002
    + surrogateDiagTailX0RatChunk001Sub000Block128Part003
    + surrogateDiagTailX0RatChunk001Sub000Block128Part004
    + surrogateDiagTailX0RatChunk001Sub000Block128Part005
    + surrogateDiagTailX0RatChunk001Sub000Block128Part006
    + surrogateDiagTailX0RatChunk001Sub000Block128Part007
    + surrogateDiagTailX0RatChunk001Sub000Block128Part008
    + surrogateDiagTailX0RatChunk001Sub000Block128Part009
    + surrogateDiagTailX0RatChunk001Sub000Block128Part010
    + surrogateDiagTailX0RatChunk001Sub000Block128Part011
    + surrogateDiagTailX0RatChunk001Sub000Block128Part012
    + surrogateDiagTailX0RatChunk001Sub000Block128Part013
    + surrogateDiagTailX0RatChunk001Sub000Block128Part014
    + surrogateDiagTailX0RatChunk001Sub000Block128Part015
    + surrogateDiagTailX0RatChunk001Sub000Block128Part016
    + surrogateDiagTailX0RatChunk001Sub000Block128Part017
    + surrogateDiagTailX0RatChunk001Sub000Block128Part018
    + surrogateDiagTailX0RatChunk001Sub000Block128Part019
    + surrogateDiagTailX0RatChunk001Sub000Block128Part020
    + surrogateDiagTailX0RatChunk001Sub000Block128Part021
    + surrogateDiagTailX0RatChunk001Sub000Block128Part022
    + surrogateDiagTailX0RatChunk001Sub000Block128Part023
    + surrogateDiagTailX0RatChunk001Sub000Block128Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block128_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block128Head + surrogateDiagTailX0RatChunk001Sub000Block128Mid + surrogateDiagTailX0RatChunk001Sub000Block128Tail =
      surrogateDiagTailX0RatChunk001Sub000Block128 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block128Head surrogateDiagTailX0RatChunk001Sub000Block128Mid surrogateDiagTailX0RatChunk001Sub000Block128Tail surrogateDiagTailX0RatChunk001Sub000Block128
  ring

def SurrogateDiagonalTailChunk001Sub000Block128HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block128HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block128Head

def SurrogateDiagonalTailChunk001Sub000Block128MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block128MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block128Mid

def SurrogateDiagonalTailChunk001Sub000Block128TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block128TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block128Tail

theorem surrogateDiagonalTailChunk001Sub000Block128_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block128HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block128MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block128TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block128Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block128 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block128HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block128MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block128TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block128Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block128_eq_head_add_mid_add_tail

/-- Block 129 covers tail-support indices [13225,13250) and q from 21797 to 21837. -/

def TailChunk001Sub000Block129Part000SupportExplicit : Finset ℕ :=
  ([21797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part000 : ℚ :=
  (23029941929 : ℚ) / 421109182813483584

def SurrogateDiagonalTailChunk001Sub000Block129Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21797
    = surrogateDiagTailX0RatChunk001Sub000Block129Part000

theorem surrogateDiagonalTailChunk001Sub000Block129Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part000] using hcert

def TailChunk001Sub000Block129Part001SupportExplicit : Finset ℕ :=
  ([21799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part001 : ℚ :=
  (7424943765625 : ℚ) / 141134588241557642802

def SurrogateDiagonalTailChunk001Sub000Block129Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21799
    = surrogateDiagTailX0RatChunk001Sub000Block129Part001

theorem surrogateDiagonalTailChunk001Sub000Block129Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part001] using hcert

def TailChunk001Sub000Block129Part002SupportExplicit : Finset ℕ :=
  ([21802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part002 : ℚ :=
  (254984191489 : ℚ) / 960788129202000000

def SurrogateDiagonalTailChunk001Sub000Block129Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21802
    = surrogateDiagTailX0RatChunk001Sub000Block129Part002

theorem surrogateDiagonalTailChunk001Sub000Block129Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part002] using hcert

def TailChunk001Sub000Block129Part003SupportExplicit : Finset ℕ :=
  ([21803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part003 : ℚ :=
  (7427668890625 : ℚ) / 141238211282893817202

def SurrogateDiagonalTailChunk001Sub000Block129Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21803
    = surrogateDiagTailX0RatChunk001Sub000Block129Part003

theorem surrogateDiagonalTailChunk001Sub000Block129Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part003] using hcert

def TailChunk001Sub000Block129Part004SupportExplicit : Finset ℕ :=
  ([21806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part004 : ℚ :=
  (1857428265625 : ℚ) / 8830627762265983602

def SurrogateDiagonalTailChunk001Sub000Block129Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21806
    = surrogateDiagTailX0RatChunk001Sub000Block129Part004

theorem surrogateDiagonalTailChunk001Sub000Block129Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part004] using hcert

def TailChunk001Sub000Block129Part005SupportExplicit : Finset ℕ :=
  ([21809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part005 : ℚ :=
  (9665363298475 : ℚ) / 178230739754733797376

def SurrogateDiagonalTailChunk001Sub000Block129Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21809
    = surrogateDiagTailX0RatChunk001Sub000Block129Part005

theorem surrogateDiagonalTailChunk001Sub000Block129Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part005] using hcert

def TailChunk001Sub000Block129Part006SupportExplicit : Finset ℕ :=
  ([21810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part006 : ℚ :=
  (401159977975 : ℚ) / 474222372860510208

def SurrogateDiagonalTailChunk001Sub000Block129Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21810
    = surrogateDiagTailX0RatChunk001Sub000Block129Part006

theorem surrogateDiagonalTailChunk001Sub000Block129Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part006] using hcert

def TailChunk001Sub000Block129Part007SupportExplicit : Finset ℕ :=
  ([21811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part007 : ℚ :=
  (6652842510325 : ℚ) / 110662097830040174592

def SurrogateDiagonalTailChunk001Sub000Block129Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21811
    = surrogateDiagTailX0RatChunk001Sub000Block129Part007

theorem surrogateDiagonalTailChunk001Sub000Block129Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part007] using hcert

def TailChunk001Sub000Block129Part008SupportExplicit : Finset ℕ :=
  ([21813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part008 : ℚ :=
  (148541395553 : ℚ) / 1012188317184000000

def SurrogateDiagonalTailChunk001Sub000Block129Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21813
    = surrogateDiagTailX0RatChunk001Sub000Block129Part008

theorem surrogateDiagonalTailChunk001Sub000Block129Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part008] using hcert

def TailChunk001Sub000Block129Part009SupportExplicit : Finset ℕ :=
  ([21814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part009 : ℚ :=
  (6544269551275 : ℚ) / 25569834530503477248

def SurrogateDiagonalTailChunk001Sub000Block129Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21814
    = surrogateDiagTailX0RatChunk001Sub000Block129Part009

theorem surrogateDiagonalTailChunk001Sub000Block129Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part009] using hcert

def TailChunk001Sub000Block129Part010SupportExplicit : Finset ℕ :=
  ([21815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part010 : ℚ :=
  (396422796875 : ℚ) / 4828010787448154496

def SurrogateDiagonalTailChunk001Sub000Block129Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21815
    = surrogateDiagTailX0RatChunk001Sub000Block129Part010

theorem surrogateDiagonalTailChunk001Sub000Block129Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part010] using hcert

def TailChunk001Sub000Block129Part011SupportExplicit : Finset ℕ :=
  ([21817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part011 : ℚ :=
  (7437210765625 : ℚ) / 141601341339019694592

def SurrogateDiagonalTailChunk001Sub000Block129Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21817
    = surrogateDiagTailX0RatChunk001Sub000Block129Part011

theorem surrogateDiagonalTailChunk001Sub000Block129Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part011] using hcert

def TailChunk001Sub000Block129Part012SupportExplicit : Finset ℕ :=
  ([21818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part012 : ℚ :=
  (1859473140625 : ℚ) / 8850083833688730912

def SurrogateDiagonalTailChunk001Sub000Block129Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21818
    = surrogateDiagTailX0RatChunk001Sub000Block129Part012

theorem surrogateDiagonalTailChunk001Sub000Block129Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part012] using hcert

def TailChunk001Sub000Block129Part013SupportExplicit : Finset ℕ :=
  ([21819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part013 : ℚ :=
  (10171871122825 : ℚ) / 60192344172992514048

def SurrogateDiagonalTailChunk001Sub000Block129Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21819
    = surrogateDiagTailX0RatChunk001Sub000Block129Part013

theorem surrogateDiagonalTailChunk001Sub000Block129Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part013] using hcert

def TailChunk001Sub000Block129Part014SupportExplicit : Finset ℕ :=
  ([21821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part014 : ℚ :=
  (11903901025 : ℚ) / 226728354037246752

def SurrogateDiagonalTailChunk001Sub000Block129Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21821
    = surrogateDiagTailX0RatChunk001Sub000Block129Part014

theorem surrogateDiagonalTailChunk001Sub000Block129Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part014] using hcert

def TailChunk001Sub000Block129Part015SupportExplicit : Finset ℕ :=
  ([21822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part015 : ℚ :=
  (3305748636325 : ℚ) / 6992658831556528128

def SurrogateDiagonalTailChunk001Sub000Block129Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21822
    = surrogateDiagTailX0RatChunk001Sub000Block129Part015

theorem surrogateDiagonalTailChunk001Sub000Block129Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part015] using hcert

def TailChunk001Sub000Block129Part016SupportExplicit : Finset ℕ :=
  ([21823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part016 : ℚ :=
  (29057326813225 : ℚ) / 537083237199622883328

def SurrogateDiagonalTailChunk001Sub000Block129Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21823
    = surrogateDiagTailX0RatChunk001Sub000Block129Part016

theorem surrogateDiagonalTailChunk001Sub000Block129Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part016] using hcert

def TailChunk001Sub000Block129Part017SupportExplicit : Finset ℕ :=
  ([21826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part017 : ℚ :=
  (360470523175 : ℚ) / 1193388067557974088

def SurrogateDiagonalTailChunk001Sub000Block129Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21826
    = surrogateDiagTailX0RatChunk001Sub000Block129Part017

theorem surrogateDiagonalTailChunk001Sub000Block129Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part017] using hcert

def TailChunk001Sub000Block129Part018SupportExplicit : Finset ℕ :=
  ([21827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part018 : ℚ :=
  (23224099172275 : ℚ) / 326416836970621698048

def SurrogateDiagonalTailChunk001Sub000Block129Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21827
    = surrogateDiagTailX0RatChunk001Sub000Block129Part018

theorem surrogateDiagonalTailChunk001Sub000Block129Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part018] using hcert

def TailChunk001Sub000Block129Part019SupportExplicit : Finset ℕ :=
  ([21829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part019 : ℚ :=
  (28952207635975 : ℚ) / 532705810267605744768

def SurrogateDiagonalTailChunk001Sub000Block129Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21829
    = surrogateDiagTailX0RatChunk001Sub000Block129Part019

theorem surrogateDiagonalTailChunk001Sub000Block129Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part019] using hcert

def TailChunk001Sub000Block129Part020SupportExplicit : Finset ℕ :=
  ([21830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part020 : ℚ :=
  (2372055389825 : ℚ) / 6083574150107234304

def SurrogateDiagonalTailChunk001Sub000Block129Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21830
    = surrogateDiagTailX0RatChunk001Sub000Block129Part020

theorem surrogateDiagonalTailChunk001Sub000Block129Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part020] using hcert

def TailChunk001Sub000Block129Part021SupportExplicit : Finset ℕ :=
  ([21831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part021 : ℚ :=
  (12022173551125 : ℚ) / 89431458513134635008

def SurrogateDiagonalTailChunk001Sub000Block129Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21831
    = surrogateDiagTailX0RatChunk001Sub000Block129Part021

theorem surrogateDiagonalTailChunk001Sub000Block129Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part021] using hcert

def TailChunk001Sub000Block129Part022SupportExplicit : Finset ℕ :=
  ([21833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part022 : ℚ :=
  (2430688594625 : ℚ) / 34032495392290207872

def SurrogateDiagonalTailChunk001Sub000Block129Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21833
    = surrogateDiagTailX0RatChunk001Sub000Block129Part022

theorem surrogateDiagonalTailChunk001Sub000Block129Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part022] using hcert

def TailChunk001Sub000Block129Part023SupportExplicit : Finset ℕ :=
  ([21835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part023 : ℚ :=
  (644215832371 : ℚ) / 6296621083538227200

def SurrogateDiagonalTailChunk001Sub000Block129Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21835
    = surrogateDiagTailX0RatChunk001Sub000Block129Part023

theorem surrogateDiagonalTailChunk001Sub000Block129Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part023] using hcert

def TailChunk001Sub000Block129Part024SupportExplicit : Finset ℕ :=
  ([21837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block129Part024 : ℚ :=
  (165277946943 : ℚ) / 1280789440000000000

def SurrogateDiagonalTailChunk001Sub000Block129Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 21837
    = surrogateDiagTailX0RatChunk001Sub000Block129Part024

theorem surrogateDiagonalTailChunk001Sub000Block129Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block129Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block129Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block129Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block129Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block129Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block129Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block129HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block129Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block129Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block129Part000
    + surrogateDiagTailX0RatChunk001Sub000Block129Part001
    + surrogateDiagTailX0RatChunk001Sub000Block129Part002
    + surrogateDiagTailX0RatChunk001Sub000Block129Part003
    + surrogateDiagTailX0RatChunk001Sub000Block129Part004
    + surrogateDiagTailX0RatChunk001Sub000Block129Part005
    + surrogateDiagTailX0RatChunk001Sub000Block129Part006
    + surrogateDiagTailX0RatChunk001Sub000Block129Part007
    + surrogateDiagTailX0RatChunk001Sub000Block129Part008
    + surrogateDiagTailX0RatChunk001Sub000Block129Part009

def surrogateDiagonalTailChunk001Sub000Block129MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block129Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block129Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block129Part010
    + surrogateDiagTailX0RatChunk001Sub000Block129Part011
    + surrogateDiagTailX0RatChunk001Sub000Block129Part012
    + surrogateDiagTailX0RatChunk001Sub000Block129Part013
    + surrogateDiagTailX0RatChunk001Sub000Block129Part014
    + surrogateDiagTailX0RatChunk001Sub000Block129Part015
    + surrogateDiagTailX0RatChunk001Sub000Block129Part016
    + surrogateDiagTailX0RatChunk001Sub000Block129Part017
    + surrogateDiagTailX0RatChunk001Sub000Block129Part018
    + surrogateDiagTailX0RatChunk001Sub000Block129Part019

def surrogateDiagonalTailChunk001Sub000Block129TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block129Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block129Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block129Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block129Part020
    + surrogateDiagTailX0RatChunk001Sub000Block129Part021
    + surrogateDiagTailX0RatChunk001Sub000Block129Part022
    + surrogateDiagTailX0RatChunk001Sub000Block129Part023
    + surrogateDiagTailX0RatChunk001Sub000Block129Part024

def surrogateDiagonalTailChunk001Sub000Block129Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block129HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block129MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block129TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block129 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block129Part000
    + surrogateDiagTailX0RatChunk001Sub000Block129Part001
    + surrogateDiagTailX0RatChunk001Sub000Block129Part002
    + surrogateDiagTailX0RatChunk001Sub000Block129Part003
    + surrogateDiagTailX0RatChunk001Sub000Block129Part004
    + surrogateDiagTailX0RatChunk001Sub000Block129Part005
    + surrogateDiagTailX0RatChunk001Sub000Block129Part006
    + surrogateDiagTailX0RatChunk001Sub000Block129Part007
    + surrogateDiagTailX0RatChunk001Sub000Block129Part008
    + surrogateDiagTailX0RatChunk001Sub000Block129Part009
    + surrogateDiagTailX0RatChunk001Sub000Block129Part010
    + surrogateDiagTailX0RatChunk001Sub000Block129Part011
    + surrogateDiagTailX0RatChunk001Sub000Block129Part012
    + surrogateDiagTailX0RatChunk001Sub000Block129Part013
    + surrogateDiagTailX0RatChunk001Sub000Block129Part014
    + surrogateDiagTailX0RatChunk001Sub000Block129Part015
    + surrogateDiagTailX0RatChunk001Sub000Block129Part016
    + surrogateDiagTailX0RatChunk001Sub000Block129Part017
    + surrogateDiagTailX0RatChunk001Sub000Block129Part018
    + surrogateDiagTailX0RatChunk001Sub000Block129Part019
    + surrogateDiagTailX0RatChunk001Sub000Block129Part020
    + surrogateDiagTailX0RatChunk001Sub000Block129Part021
    + surrogateDiagTailX0RatChunk001Sub000Block129Part022
    + surrogateDiagTailX0RatChunk001Sub000Block129Part023
    + surrogateDiagTailX0RatChunk001Sub000Block129Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block129_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block129Head + surrogateDiagTailX0RatChunk001Sub000Block129Mid + surrogateDiagTailX0RatChunk001Sub000Block129Tail =
      surrogateDiagTailX0RatChunk001Sub000Block129 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block129Head surrogateDiagTailX0RatChunk001Sub000Block129Mid surrogateDiagTailX0RatChunk001Sub000Block129Tail surrogateDiagTailX0RatChunk001Sub000Block129
  ring

def SurrogateDiagonalTailChunk001Sub000Block129HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block129HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block129Head

def SurrogateDiagonalTailChunk001Sub000Block129MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block129MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block129Mid

def SurrogateDiagonalTailChunk001Sub000Block129TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block129TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block129Tail

theorem surrogateDiagonalTailChunk001Sub000Block129_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block129HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block129MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block129TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block129Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block129 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block129HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block129MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block129TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block129Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block129_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
