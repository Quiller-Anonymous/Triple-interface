import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [158,159). -/

/- Block 158 covers tail-support indices [3950,3975) and q from 6546 to 6586. -/

def TailChunk000Sub000Block158Part000SupportExplicit : Finset ℕ :=
  ([6546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part000 : ℚ :=
  (14865522467 : ℚ) / 1129491141057600

def SurrogateDiagonalTailChunk000Sub000Block158Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6546
    = surrogateDiagTailX0RatChunk000Sub000Block158Part000

theorem surrogateDiagonalTailChunk000Sub000Block158Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part000] using hcert

def TailChunk000Sub000Block158Part001SupportExplicit : Finset ℕ :=
  ([6547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part001 : ℚ :=
  (669737640625 : ℚ) / 1147812292313561682

def SurrogateDiagonalTailChunk000Sub000Block158Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6547
    = surrogateDiagTailX0RatChunk000Sub000Block158Part001

theorem surrogateDiagonalTailChunk000Sub000Block158Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part001] using hcert

def TailChunk000Sub000Block158Part002SupportExplicit : Finset ℕ :=
  ([6549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part002 : ℚ :=
  (177478147325 : ℚ) / 95055846095425536

def SurrogateDiagonalTailChunk000Sub000Block158Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6549
    = surrogateDiagTailX0RatChunk000Sub000Block158Part002

theorem surrogateDiagonalTailChunk000Sub000Block158Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part002] using hcert

def TailChunk000Sub000Block158Part003SupportExplicit : Finset ℕ :=
  ([6551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part003 : ℚ :=
  (42915601 : ℚ) / 73639705246050

def SurrogateDiagonalTailChunk000Sub000Block158Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6551
    = surrogateDiagTailX0RatChunk000Sub000Block158Part003

theorem surrogateDiagonalTailChunk000Sub000Block158Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part003] using hcert

def TailChunk000Sub000Block158Part004SupportExplicit : Finset ℕ :=
  ([6553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part004 : ℚ :=
  (670965765625 : ℚ) / 1152026376153149952

def SurrogateDiagonalTailChunk000Sub000Block158Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6553
    = surrogateDiagTailX0RatChunk000Sub000Block158Part004

theorem surrogateDiagonalTailChunk000Sub000Block158Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part004] using hcert

def TailChunk000Sub000Block158Part005SupportExplicit : Finset ℕ :=
  ([6554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part005 : ℚ :=
  (423960000525 : ℚ) / 80613879196942336

def SurrogateDiagonalTailChunk000Sub000Block158Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6554
    = surrogateDiagTailX0RatChunk000Sub000Block158Part005

theorem surrogateDiagonalTailChunk000Sub000Block158Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part005] using hcert

def TailChunk000Sub000Block158Part006SupportExplicit : Finset ℕ :=
  ([6555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part006 : ℚ :=
  (49933111775 : ℚ) / 10494368472563712

def SurrogateDiagonalTailChunk000Sub000Block158Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6555
    = surrogateDiagTailX0RatChunk000Sub000Block158Part006

theorem surrogateDiagonalTailChunk000Sub000Block158Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part006] using hcert

def TailChunk000Sub000Block158Part007SupportExplicit : Finset ℕ :=
  ([6557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part007 : ℚ :=
  (200458864825 : ℚ) / 321897294762915456

def SurrogateDiagonalTailChunk000Sub000Block158Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6557
    = surrogateDiagTailX0RatChunk000Sub000Block158Part007

theorem surrogateDiagonalTailChunk000Sub000Block158Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part007] using hcert

def TailChunk000Sub000Block158Part008SupportExplicit : Finset ℕ :=
  ([6558] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part008 : ℚ :=
  (820592593075 : ℚ) / 56890191414970368

def SurrogateDiagonalTailChunk000Sub000Block158Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6558
    = surrogateDiagTailX0RatChunk000Sub000Block158Part008

theorem surrogateDiagonalTailChunk000Sub000Block158Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part008] using hcert

def TailChunk000Sub000Block158Part009SupportExplicit : Finset ℕ :=
  ([6559] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part009 : ℚ :=
  (275435241775 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub000Block158Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6559
    = surrogateDiagTailX0RatChunk000Sub000Block158Part009

theorem surrogateDiagonalTailChunk000Sub000Block158Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part009] using hcert

def TailChunk000Sub000Block158Part010SupportExplicit : Finset ℕ :=
  ([6562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part010 : ℚ :=
  (217499173825 : ℚ) / 74231878281854976

def SurrogateDiagonalTailChunk000Sub000Block158Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6562
    = surrogateDiagTailX0RatChunk000Sub000Block158Part010

theorem surrogateDiagonalTailChunk000Sub000Block158Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part010] using hcert

def TailChunk000Sub000Block158Part011SupportExplicit : Finset ℕ :=
  ([6563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block158Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6563
    = surrogateDiagTailX0RatChunk000Sub000Block158Part011

theorem surrogateDiagonalTailChunk000Sub000Block158Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part011] using hcert

def TailChunk000Sub000Block158Part012SupportExplicit : Finset ℕ :=
  ([6565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part012 : ℚ :=
  (994443449 : ℚ) / 2654738841600000

def SurrogateDiagonalTailChunk000Sub000Block158Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6565
    = surrogateDiagTailX0RatChunk000Sub000Block158Part012

theorem surrogateDiagonalTailChunk000Sub000Block158Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part012] using hcert

def TailChunk000Sub000Block158Part013SupportExplicit : Finset ℕ :=
  ([6567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part013 : ℚ :=
  (764201363 : ℚ) / 768630503361600

def SurrogateDiagonalTailChunk000Sub000Block158Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6567
    = surrogateDiagTailX0RatChunk000Sub000Block158Part013

theorem surrogateDiagonalTailChunk000Sub000Block158Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part013] using hcert

def TailChunk000Sub000Block158Part014SupportExplicit : Finset ℕ :=
  ([6569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block158Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6569
    = surrogateDiagTailX0RatChunk000Sub000Block158Part014

theorem surrogateDiagonalTailChunk000Sub000Block158Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part014] using hcert

def TailChunk000Sub000Block158Part015SupportExplicit : Finset ℕ :=
  ([6571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block158Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6571
    = surrogateDiagTailX0RatChunk000Sub000Block158Part015

theorem surrogateDiagonalTailChunk000Sub000Block158Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part015] using hcert

def TailChunk000Sub000Block158Part016SupportExplicit : Finset ℕ :=
  ([6573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part016 : ℚ :=
  (154535812075 : ℚ) / 122831633608998912

def SurrogateDiagonalTailChunk000Sub000Block158Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6573
    = surrogateDiagTailX0RatChunk000Sub000Block158Part016

theorem surrogateDiagonalTailChunk000Sub000Block158Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part016] using hcert

def TailChunk000Sub000Block158Part017SupportExplicit : Finset ℕ :=
  ([6574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part017 : ℚ :=
  (656541926125 : ℚ) / 229736852599523328

def SurrogateDiagonalTailChunk000Sub000Block158Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6574
    = surrogateDiagTailX0RatChunk000Sub000Block158Part017

theorem surrogateDiagonalTailChunk000Sub000Block158Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part017] using hcert

def TailChunk000Sub000Block158Part018SupportExplicit : Finset ℕ :=
  ([6577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block158Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6577
    = surrogateDiagTailX0RatChunk000Sub000Block158Part018

theorem surrogateDiagonalTailChunk000Sub000Block158Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part018] using hcert

def TailChunk000Sub000Block158Part019SupportExplicit : Finset ℕ :=
  ([6578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part019 : ℚ :=
  (727736077 : ℚ) / 147227391590400

def SurrogateDiagonalTailChunk000Sub000Block158Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6578
    = surrogateDiagTailX0RatChunk000Sub000Block158Part019

theorem surrogateDiagonalTailChunk000Sub000Block158Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part019] using hcert

def TailChunk000Sub000Block158Part020SupportExplicit : Finset ℕ :=
  ([6581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part020 : ℚ :=
  (1082739025 : ℚ) / 1874953168610592

def SurrogateDiagonalTailChunk000Sub000Block158Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6581
    = surrogateDiagTailX0RatChunk000Sub000Block158Part020

theorem surrogateDiagonalTailChunk000Sub000Block158Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part020] using hcert

def TailChunk000Sub000Block158Part021SupportExplicit : Finset ℕ :=
  ([6582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part021 : ℚ :=
  (826610686975 : ℚ) / 57728338505269248

def SurrogateDiagonalTailChunk000Sub000Block158Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6582
    = surrogateDiagTailX0RatChunk000Sub000Block158Part021

theorem surrogateDiagonalTailChunk000Sub000Block158Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part021] using hcert

def TailChunk000Sub000Block158Part022SupportExplicit : Finset ℕ :=
  ([6583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part022 : ℚ :=
  (214910363175 : ℚ) / 334126941101868544

def SurrogateDiagonalTailChunk000Sub000Block158Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6583
    = surrogateDiagTailX0RatChunk000Sub000Block158Part022

theorem surrogateDiagonalTailChunk000Sub000Block158Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part022] using hcert

def TailChunk000Sub000Block158Part023SupportExplicit : Finset ℕ :=
  ([6585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part023 : ℚ :=
  (684827687525 : ℚ) / 188474783539544064

def SurrogateDiagonalTailChunk000Sub000Block158Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6585
    = surrogateDiagTailX0RatChunk000Sub000Block158Part023

theorem surrogateDiagonalTailChunk000Sub000Block158Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part023] using hcert

def TailChunk000Sub000Block158Part024SupportExplicit : Finset ℕ :=
  ([6586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block158Part024 : ℚ :=
  (1292451289825 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub000Block158Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6586
    = surrogateDiagTailX0RatChunk000Sub000Block158Part024

theorem surrogateDiagonalTailChunk000Sub000Block158Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block158Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block158Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block158Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block158Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block158Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block158Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block158HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block158Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block158Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block158Part000
    + surrogateDiagTailX0RatChunk000Sub000Block158Part001
    + surrogateDiagTailX0RatChunk000Sub000Block158Part002
    + surrogateDiagTailX0RatChunk000Sub000Block158Part003
    + surrogateDiagTailX0RatChunk000Sub000Block158Part004
    + surrogateDiagTailX0RatChunk000Sub000Block158Part005
    + surrogateDiagTailX0RatChunk000Sub000Block158Part006
    + surrogateDiagTailX0RatChunk000Sub000Block158Part007
    + surrogateDiagTailX0RatChunk000Sub000Block158Part008
    + surrogateDiagTailX0RatChunk000Sub000Block158Part009

def surrogateDiagonalTailChunk000Sub000Block158MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block158Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block158Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block158Part010
    + surrogateDiagTailX0RatChunk000Sub000Block158Part011
    + surrogateDiagTailX0RatChunk000Sub000Block158Part012
    + surrogateDiagTailX0RatChunk000Sub000Block158Part013
    + surrogateDiagTailX0RatChunk000Sub000Block158Part014
    + surrogateDiagTailX0RatChunk000Sub000Block158Part015
    + surrogateDiagTailX0RatChunk000Sub000Block158Part016
    + surrogateDiagTailX0RatChunk000Sub000Block158Part017
    + surrogateDiagTailX0RatChunk000Sub000Block158Part018
    + surrogateDiagTailX0RatChunk000Sub000Block158Part019

def surrogateDiagonalTailChunk000Sub000Block158TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block158Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block158Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block158Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block158Part020
    + surrogateDiagTailX0RatChunk000Sub000Block158Part021
    + surrogateDiagTailX0RatChunk000Sub000Block158Part022
    + surrogateDiagTailX0RatChunk000Sub000Block158Part023
    + surrogateDiagTailX0RatChunk000Sub000Block158Part024

def surrogateDiagonalTailChunk000Sub000Block158Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block158HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block158MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block158TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block158 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block158Part000
    + surrogateDiagTailX0RatChunk000Sub000Block158Part001
    + surrogateDiagTailX0RatChunk000Sub000Block158Part002
    + surrogateDiagTailX0RatChunk000Sub000Block158Part003
    + surrogateDiagTailX0RatChunk000Sub000Block158Part004
    + surrogateDiagTailX0RatChunk000Sub000Block158Part005
    + surrogateDiagTailX0RatChunk000Sub000Block158Part006
    + surrogateDiagTailX0RatChunk000Sub000Block158Part007
    + surrogateDiagTailX0RatChunk000Sub000Block158Part008
    + surrogateDiagTailX0RatChunk000Sub000Block158Part009
    + surrogateDiagTailX0RatChunk000Sub000Block158Part010
    + surrogateDiagTailX0RatChunk000Sub000Block158Part011
    + surrogateDiagTailX0RatChunk000Sub000Block158Part012
    + surrogateDiagTailX0RatChunk000Sub000Block158Part013
    + surrogateDiagTailX0RatChunk000Sub000Block158Part014
    + surrogateDiagTailX0RatChunk000Sub000Block158Part015
    + surrogateDiagTailX0RatChunk000Sub000Block158Part016
    + surrogateDiagTailX0RatChunk000Sub000Block158Part017
    + surrogateDiagTailX0RatChunk000Sub000Block158Part018
    + surrogateDiagTailX0RatChunk000Sub000Block158Part019
    + surrogateDiagTailX0RatChunk000Sub000Block158Part020
    + surrogateDiagTailX0RatChunk000Sub000Block158Part021
    + surrogateDiagTailX0RatChunk000Sub000Block158Part022
    + surrogateDiagTailX0RatChunk000Sub000Block158Part023
    + surrogateDiagTailX0RatChunk000Sub000Block158Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block158_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block158Head + surrogateDiagTailX0RatChunk000Sub000Block158Mid + surrogateDiagTailX0RatChunk000Sub000Block158Tail =
      surrogateDiagTailX0RatChunk000Sub000Block158 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block158Head surrogateDiagTailX0RatChunk000Sub000Block158Mid surrogateDiagTailX0RatChunk000Sub000Block158Tail surrogateDiagTailX0RatChunk000Sub000Block158
  ring

def SurrogateDiagonalTailChunk000Sub000Block158HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block158HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block158Head

def SurrogateDiagonalTailChunk000Sub000Block158MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block158MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block158Mid

def SurrogateDiagonalTailChunk000Sub000Block158TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block158TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block158Tail

theorem surrogateDiagonalTailChunk000Sub000Block158_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block158HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block158MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block158TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block158Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block158 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block158HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block158MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block158TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block158Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block158_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
