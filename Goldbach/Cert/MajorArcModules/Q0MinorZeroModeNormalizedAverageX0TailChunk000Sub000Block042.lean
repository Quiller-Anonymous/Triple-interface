import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [42,43). -/

/- Block 042 covers tail-support indices [1050,1075) and q from 1778 to 1819. -/

def TailChunk000Sub000Block042Part000SupportExplicit : Finset ℕ :=
  ([1778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part000 : ℚ :=
  (9221372875 : ℚ) / 30251734257024

def SurrogateDiagonalTailChunk000Sub000Block042Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1778
    = surrogateDiagTailX0RatChunk000Sub000Block042Part000

theorem surrogateDiagonalTailChunk000Sub000Block042Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part000] using hcert

def TailChunk000Sub000Block042Part001SupportExplicit : Finset ℕ :=
  ([1779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part001 : ℚ :=
  (19207757725 : ℚ) / 307123950747648

def SurrogateDiagonalTailChunk000Sub000Block042Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1779
    = surrogateDiagTailX0RatChunk000Sub000Block042Part001

theorem surrogateDiagonalTailChunk000Sub000Block042Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part001] using hcert

def TailChunk000Sub000Block042Part002SupportExplicit : Finset ℕ :=
  ([1781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part002 : ℚ :=
  (180842649275 : ℚ) / 5912705141047296

def SurrogateDiagonalTailChunk000Sub000Block042Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1781
    = surrogateDiagTailX0RatChunk000Sub000Block042Part002

theorem surrogateDiagonalTailChunk000Sub000Block042Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part002] using hcert

def TailChunk000Sub000Block042Part003SupportExplicit : Finset ℕ :=
  ([1783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part003 : ℚ :=
  (66204528425 : ℚ) / 2801658184753032

def SurrogateDiagonalTailChunk000Sub000Block042Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1783
    = surrogateDiagTailX0RatChunk000Sub000Block042Part003

theorem surrogateDiagonalTailChunk000Sub000Block042Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part003] using hcert

def TailChunk000Sub000Block042Part004SupportExplicit : Finset ℕ :=
  ([1785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part004 : ℚ :=
  (8032563575 : ℚ) / 32218697170944

def SurrogateDiagonalTailChunk000Sub000Block042Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1785
    = surrogateDiagTailX0RatChunk000Sub000Block042Part004

theorem surrogateDiagonalTailChunk000Sub000Block042Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part004] using hcert

def TailChunk000Sub000Block042Part005SupportExplicit : Finset ℕ :=
  ([1786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part005 : ℚ :=
  (275866482625 : ℚ) / 1175298565350528

def SurrogateDiagonalTailChunk000Sub000Block042Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1786
    = surrogateDiagTailX0RatChunk000Sub000Block042Part005

theorem surrogateDiagonalTailChunk000Sub000Block042Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part005] using hcert

def TailChunk000Sub000Block042Part006SupportExplicit : Finset ℕ :=
  ([1787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part006 : ℚ :=
  (199505728275 : ℚ) / 8480694567766936

def SurrogateDiagonalTailChunk000Sub000Block042Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1787
    = surrogateDiagTailX0RatChunk000Sub000Block042Part006

theorem surrogateDiagonalTailChunk000Sub000Block042Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part006] using hcert

def TailChunk000Sub000Block042Part007SupportExplicit : Finset ℕ :=
  ([1789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part007 : ℚ :=
  (66650849825 : ℚ) / 2839581952589952

def SurrogateDiagonalTailChunk000Sub000Block042Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1789
    = surrogateDiagTailX0RatChunk000Sub000Block042Part007

theorem surrogateDiagonalTailChunk000Sub000Block042Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part007] using hcert

def TailChunk000Sub000Block042Part008SupportExplicit : Finset ℕ :=
  ([1790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part008 : ℚ :=
  (78319513725 : ℚ) / 214203014649856

def SurrogateDiagonalTailChunk000Sub000Block042Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1790
    = surrogateDiagTailX0RatChunk000Sub000Block042Part008

theorem surrogateDiagonalTailChunk000Sub000Block042Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part008] using hcert

def TailChunk000Sub000Block042Part009SupportExplicit : Finset ℕ :=
  ([1793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part009 : ℚ :=
  (21648652033 : ℚ) / 688885285507200

def SurrogateDiagonalTailChunk000Sub000Block042Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1793
    = surrogateDiagTailX0RatChunk000Sub000Block042Part009

theorem surrogateDiagonalTailChunk000Sub000Block042Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part009] using hcert

def TailChunk000Sub000Block042Part010SupportExplicit : Finset ℕ :=
  ([1794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part010 : ℚ :=
  (154420450975 : ℚ) / 194340156899328

def SurrogateDiagonalTailChunk000Sub000Block042Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1794
    = surrogateDiagTailX0RatChunk000Sub000Block042Part010

theorem surrogateDiagonalTailChunk000Sub000Block042Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part010] using hcert

def TailChunk000Sub000Block042Part011SupportExplicit : Finset ℕ :=
  ([1795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part011 : ℚ :=
  (3702697325 : ℚ) / 82146480490896

def SurrogateDiagonalTailChunk000Sub000Block042Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1795
    = surrogateDiagTailX0RatChunk000Sub000Block042Part011

theorem surrogateDiagonalTailChunk000Sub000Block042Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part011] using hcert

def TailChunk000Sub000Block042Part012SupportExplicit : Finset ℕ :=
  ([1797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part012 : ℚ :=
  (1549725 : ℚ) / 19673941664

def SurrogateDiagonalTailChunk000Sub000Block042Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1797
    = surrogateDiagTailX0RatChunk000Sub000Block042Part012

theorem surrogateDiagonalTailChunk000Sub000Block042Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part012] using hcert

def TailChunk000Sub000Block042Part013SupportExplicit : Finset ℕ :=
  ([1798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part013 : ℚ :=
  (198162247 : ℚ) / 1037439446400

def SurrogateDiagonalTailChunk000Sub000Block042Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1798
    = surrogateDiagTailX0RatChunk000Sub000Block042Part013

theorem surrogateDiagonalTailChunk000Sub000Block042Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part013] using hcert

def TailChunk000Sub000Block042Part014SupportExplicit : Finset ℕ :=
  ([1799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part014 : ℚ :=
  (509869300525 : ℚ) / 13918477177847808

def SurrogateDiagonalTailChunk000Sub000Block042Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1799
    = surrogateDiagTailX0RatChunk000Sub000Block042Part014

theorem surrogateDiagonalTailChunk000Sub000Block042Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part014] using hcert

def TailChunk000Sub000Block042Part015SupportExplicit : Finset ℕ :=
  ([1801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part015 : ℚ :=
  (2701919633 : ℚ) / 116663328000000

def SurrogateDiagonalTailChunk000Sub000Block042Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1801
    = surrogateDiagTailX0RatChunk000Sub000Block042Part015

theorem surrogateDiagonalTailChunk000Sub000Block042Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part015] using hcert

def TailChunk000Sub000Block042Part016SupportExplicit : Finset ℕ :=
  ([1802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part016 : ℚ :=
  (279575780875 : ℚ) / 1198174752473088

def SurrogateDiagonalTailChunk000Sub000Block042Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1802
    = surrogateDiagTailX0RatChunk000Sub000Block042Part016

theorem surrogateDiagonalTailChunk000Sub000Block042Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part016] using hcert

def TailChunk000Sub000Block042Part017SupportExplicit : Finset ℕ :=
  ([1803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part017 : ℚ :=
  (16901 : ℚ) / 216000000

def SurrogateDiagonalTailChunk000Sub000Block042Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1803
    = surrogateDiagTailX0RatChunk000Sub000Block042Part017

theorem surrogateDiagonalTailChunk000Sub000Block042Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part017] using hcert

def TailChunk000Sub000Block042Part018SupportExplicit : Finset ℕ :=
  ([1806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part018 : ℚ :=
  (160683476125 : ℚ) / 161342582704128

def SurrogateDiagonalTailChunk000Sub000Block042Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1806
    = surrogateDiagTailX0RatChunk000Sub000Block042Part018

theorem surrogateDiagonalTailChunk000Sub000Block042Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part018] using hcert

def TailChunk000Sub000Block042Part019SupportExplicit : Finset ℕ :=
  ([1807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part019 : ℚ :=
  (557299993525 : ℚ) / 18804777045608448

def SurrogateDiagonalTailChunk000Sub000Block042Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1807
    = surrogateDiagTailX0RatChunk000Sub000Block042Part019

theorem surrogateDiagonalTailChunk000Sub000Block042Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part019] using hcert

def TailChunk000Sub000Block042Part020SupportExplicit : Finset ℕ :=
  ([1810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part020 : ℚ :=
  (9609602467 : ℚ) / 26879230771200

def SurrogateDiagonalTailChunk000Sub000Block042Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1810
    = surrogateDiagTailX0RatChunk000Sub000Block042Part020

theorem surrogateDiagonalTailChunk000Sub000Block042Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part020] using hcert

def TailChunk000Sub000Block042Part021SupportExplicit : Finset ℕ :=
  ([1811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part021 : ℚ :=
  (16395325279 : ℚ) / 1073497777624200

def SurrogateDiagonalTailChunk000Sub000Block042Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1811
    = surrogateDiagTailX0RatChunk000Sub000Block042Part021

theorem surrogateDiagonalTailChunk000Sub000Block042Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part021] using hcert

def TailChunk000Sub000Block042Part022SupportExplicit : Finset ℕ :=
  ([1814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part022 : ℚ :=
  (128436075125 : ℚ) / 842383116554724

def SurrogateDiagonalTailChunk000Sub000Block042Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1814
    = surrogateDiagTailX0RatChunk000Sub000Block042Part022

theorem surrogateDiagonalTailChunk000Sub000Block042Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part022] using hcert

def TailChunk000Sub000Block042Part023SupportExplicit : Finset ℕ :=
  ([1817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part023 : ℚ :=
  (36193962875 : ℚ) / 1971075717756288

def SurrogateDiagonalTailChunk000Sub000Block042Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1817
    = surrogateDiagTailX0RatChunk000Sub000Block042Part023

theorem surrogateDiagonalTailChunk000Sub000Block042Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part023] using hcert

def TailChunk000Sub000Block042Part024SupportExplicit : Finset ℕ :=
  ([1819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block042Part024 : ℚ :=
  (575287150375 : ℚ) / 20688559397142528

def SurrogateDiagonalTailChunk000Sub000Block042Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1819
    = surrogateDiagTailX0RatChunk000Sub000Block042Part024

theorem surrogateDiagonalTailChunk000Sub000Block042Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block042Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block042Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block042Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block042Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block042Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block042HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block042Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block042Part000
    + surrogateDiagTailX0RatChunk000Sub000Block042Part001
    + surrogateDiagTailX0RatChunk000Sub000Block042Part002
    + surrogateDiagTailX0RatChunk000Sub000Block042Part003
    + surrogateDiagTailX0RatChunk000Sub000Block042Part004
    + surrogateDiagTailX0RatChunk000Sub000Block042Part005
    + surrogateDiagTailX0RatChunk000Sub000Block042Part006
    + surrogateDiagTailX0RatChunk000Sub000Block042Part007
    + surrogateDiagTailX0RatChunk000Sub000Block042Part008
    + surrogateDiagTailX0RatChunk000Sub000Block042Part009

def surrogateDiagonalTailChunk000Sub000Block042MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block042Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block042Part010
    + surrogateDiagTailX0RatChunk000Sub000Block042Part011
    + surrogateDiagTailX0RatChunk000Sub000Block042Part012
    + surrogateDiagTailX0RatChunk000Sub000Block042Part013
    + surrogateDiagTailX0RatChunk000Sub000Block042Part014
    + surrogateDiagTailX0RatChunk000Sub000Block042Part015
    + surrogateDiagTailX0RatChunk000Sub000Block042Part016
    + surrogateDiagTailX0RatChunk000Sub000Block042Part017
    + surrogateDiagTailX0RatChunk000Sub000Block042Part018
    + surrogateDiagTailX0RatChunk000Sub000Block042Part019

def surrogateDiagonalTailChunk000Sub000Block042TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block042Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block042Part020
    + surrogateDiagTailX0RatChunk000Sub000Block042Part021
    + surrogateDiagTailX0RatChunk000Sub000Block042Part022
    + surrogateDiagTailX0RatChunk000Sub000Block042Part023
    + surrogateDiagTailX0RatChunk000Sub000Block042Part024

def surrogateDiagonalTailChunk000Sub000Block042Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block042HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block042MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block042TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block042 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block042Part000
    + surrogateDiagTailX0RatChunk000Sub000Block042Part001
    + surrogateDiagTailX0RatChunk000Sub000Block042Part002
    + surrogateDiagTailX0RatChunk000Sub000Block042Part003
    + surrogateDiagTailX0RatChunk000Sub000Block042Part004
    + surrogateDiagTailX0RatChunk000Sub000Block042Part005
    + surrogateDiagTailX0RatChunk000Sub000Block042Part006
    + surrogateDiagTailX0RatChunk000Sub000Block042Part007
    + surrogateDiagTailX0RatChunk000Sub000Block042Part008
    + surrogateDiagTailX0RatChunk000Sub000Block042Part009
    + surrogateDiagTailX0RatChunk000Sub000Block042Part010
    + surrogateDiagTailX0RatChunk000Sub000Block042Part011
    + surrogateDiagTailX0RatChunk000Sub000Block042Part012
    + surrogateDiagTailX0RatChunk000Sub000Block042Part013
    + surrogateDiagTailX0RatChunk000Sub000Block042Part014
    + surrogateDiagTailX0RatChunk000Sub000Block042Part015
    + surrogateDiagTailX0RatChunk000Sub000Block042Part016
    + surrogateDiagTailX0RatChunk000Sub000Block042Part017
    + surrogateDiagTailX0RatChunk000Sub000Block042Part018
    + surrogateDiagTailX0RatChunk000Sub000Block042Part019
    + surrogateDiagTailX0RatChunk000Sub000Block042Part020
    + surrogateDiagTailX0RatChunk000Sub000Block042Part021
    + surrogateDiagTailX0RatChunk000Sub000Block042Part022
    + surrogateDiagTailX0RatChunk000Sub000Block042Part023
    + surrogateDiagTailX0RatChunk000Sub000Block042Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block042_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block042Head + surrogateDiagTailX0RatChunk000Sub000Block042Mid + surrogateDiagTailX0RatChunk000Sub000Block042Tail =
      surrogateDiagTailX0RatChunk000Sub000Block042 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block042Head surrogateDiagTailX0RatChunk000Sub000Block042Mid surrogateDiagTailX0RatChunk000Sub000Block042Tail surrogateDiagTailX0RatChunk000Sub000Block042
  ring

def SurrogateDiagonalTailChunk000Sub000Block042HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block042HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block042Head

def SurrogateDiagonalTailChunk000Sub000Block042MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block042MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block042Mid

def SurrogateDiagonalTailChunk000Sub000Block042TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block042TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block042Tail

theorem surrogateDiagonalTailChunk000Sub000Block042_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block042HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block042MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block042TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block042Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block042 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block042HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block042MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block042TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block042Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block042_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
