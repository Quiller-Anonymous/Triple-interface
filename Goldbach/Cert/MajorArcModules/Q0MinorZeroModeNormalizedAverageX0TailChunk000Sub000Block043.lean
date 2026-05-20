import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [43,44). -/

/- Block 043 covers tail-support indices [1075,1100) and q from 1821 to 1865. -/

def TailChunk000Sub000Block043Part000SupportExplicit : Finset ℕ :=
  ([1821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part000 : ℚ :=
  (195442934675 : ℚ) / 2697785043038784

def SurrogateDiagonalTailChunk000Sub000Block043Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1821
    = surrogateDiagTailX0RatChunk000Sub000Block043Part000

theorem surrogateDiagonalTailChunk000Sub000Block043Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part000] using hcert

def TailChunk000Sub000Block043Part001SupportExplicit : Finset ℕ :=
  ([1822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part001 : ℚ :=
  (829091079 : ℚ) / 4572578399480

def SurrogateDiagonalTailChunk000Sub000Block043Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1822
    = surrogateDiagTailX0RatChunk000Sub000Block043Part001

theorem surrogateDiagonalTailChunk000Sub000Block043Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part001] using hcert

def TailChunk000Sub000Block043Part002SupportExplicit : Finset ℕ :=
  ([1823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part002 : ℚ :=
  (207624979275 : ℚ) / 9185421600189976

def SurrogateDiagonalTailChunk000Sub000Block043Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1823
    = surrogateDiagTailX0RatChunk000Sub000Block043Part002

theorem surrogateDiagonalTailChunk000Sub000Block043Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part002] using hcert

def TailChunk000Sub000Block043Part003SupportExplicit : Finset ℕ :=
  ([1826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part003 : ℚ :=
  (5559660713 : ℚ) / 22610609217600

def SurrogateDiagonalTailChunk000Sub000Block043Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1826
    = surrogateDiagTailX0RatChunk000Sub000Block043Part003

theorem surrogateDiagonalTailChunk000Sub000Block043Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part003] using hcert

def TailChunk000Sub000Block043Part004SupportExplicit : Finset ℕ :=
  ([1829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part004 : ℚ :=
  (23768651641 : ℚ) / 916819503235200

def SurrogateDiagonalTailChunk000Sub000Block043Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1829
    = surrogateDiagTailX0RatChunk000Sub000Block043Part004

theorem surrogateDiagonalTailChunk000Sub000Block043Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part004] using hcert

def TailChunk000Sub000Block043Part005SupportExplicit : Finset ℕ :=
  ([1830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part005 : ℚ :=
  (1917185903 : ℚ) / 1769825894400

def SurrogateDiagonalTailChunk000Sub000Block043Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1830
    = surrogateDiagTailX0RatChunk000Sub000Block043Part005

theorem surrogateDiagonalTailChunk000Sub000Block043Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part005] using hcert

def TailChunk000Sub000Block043Part006SupportExplicit : Finset ℕ :=
  ([1831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part006 : ℚ :=
  (16759452439 : ℚ) / 1121737423624200

def SurrogateDiagonalTailChunk000Sub000Block043Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1831
    = surrogateDiagTailX0RatChunk000Sub000Block043Part006

theorem surrogateDiagonalTailChunk000Sub000Block043Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part006] using hcert

def TailChunk000Sub000Block043Part007SupportExplicit : Finset ℕ :=
  ([1833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part007 : ℚ :=
  (356803156975 : ℚ) / 3714523860860928

def SurrogateDiagonalTailChunk000Sub000Block043Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1833
    = surrogateDiagTailX0RatChunk000Sub000Block043Part007

theorem surrogateDiagonalTailChunk000Sub000Block043Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part007] using hcert

def TailChunk000Sub000Block043Part008SupportExplicit : Finset ℕ :=
  ([1834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part008 : ℚ :=
  (1008381521 : ℚ) / 4113606556800

def SurrogateDiagonalTailChunk000Sub000Block043Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1834
    = surrogateDiagTailX0RatChunk000Sub000Block043Part008

theorem surrogateDiagonalTailChunk000Sub000Block043Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part008] using hcert

def TailChunk000Sub000Block043Part009SupportExplicit : Finset ℕ :=
  ([1835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part009 : ℚ :=
  (20637810725 : ℚ) / 478607967412992

def SurrogateDiagonalTailChunk000Sub000Block043Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1835
    = surrogateDiagTailX0RatChunk000Sub000Block043Part009

theorem surrogateDiagonalTailChunk000Sub000Block043Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part009] using hcert

def TailChunk000Sub000Block043Part010SupportExplicit : Finset ℕ :=
  ([1837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part010 : ℚ :=
  (5255014017 : ℚ) / 253161667542400

def SurrogateDiagonalTailChunk000Sub000Block043Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1837
    = surrogateDiagTailX0RatChunk000Sub000Block043Part010

theorem surrogateDiagonalTailChunk000Sub000Block043Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part010] using hcert

def TailChunk000Sub000Block043Part011SupportExplicit : Finset ℕ :=
  ([1838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part011 : ℚ :=
  (131857086125 : ℚ) / 887907221155044

def SurrogateDiagonalTailChunk000Sub000Block043Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1838
    = surrogateDiagTailX0RatChunk000Sub000Block043Part011

theorem surrogateDiagonalTailChunk000Sub000Block043Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part011] using hcert

def TailChunk000Sub000Block043Part012SupportExplicit : Finset ℕ :=
  ([1839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part012 : ℚ :=
  (732816325 : ℚ) / 10317004748352

def SurrogateDiagonalTailChunk000Sub000Block043Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1839
    = surrogateDiagTailX0RatChunk000Sub000Block043Part012

theorem surrogateDiagonalTailChunk000Sub000Block043Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part012] using hcert

def TailChunk000Sub000Block043Part013SupportExplicit : Finset ℕ :=
  ([1841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part013 : ℚ :=
  (533960961025 : ℚ) / 15269929279820928

def SurrogateDiagonalTailChunk000Sub000Block043Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1841
    = surrogateDiagTailX0RatChunk000Sub000Block043Part013

theorem surrogateDiagonalTailChunk000Sub000Block043Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part013] using hcert

def TailChunk000Sub000Block043Part014SupportExplicit : Finset ℕ :=
  ([1842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part014 : ℚ :=
  (99817353725 : ℚ) / 175389080721984

def SurrogateDiagonalTailChunk000Sub000Block043Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1842
    = surrogateDiagTailX0RatChunk000Sub000Block043Part014

theorem surrogateDiagonalTailChunk000Sub000Block043Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part014] using hcert

def TailChunk000Sub000Block043Part015SupportExplicit : Finset ℕ :=
  ([1843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part015 : ℚ :=
  (16493605675 : ℚ) / 619297476968448

def SurrogateDiagonalTailChunk000Sub000Block043Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1843
    = surrogateDiagTailX0RatChunk000Sub000Block043Part015

theorem surrogateDiagonalTailChunk000Sub000Block043Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part015] using hcert

def TailChunk000Sub000Block043Part016SupportExplicit : Finset ℕ :=
  ([1846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part016 : ℚ :=
  (959830343 : ℚ) / 4149757785600

def SurrogateDiagonalTailChunk000Sub000Block043Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1846
    = surrogateDiagTailX0RatChunk000Sub000Block043Part016

theorem surrogateDiagonalTailChunk000Sub000Block043Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part016] using hcert

def TailChunk000Sub000Block043Part017SupportExplicit : Finset ℕ :=
  ([1847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part017 : ℚ :=
  (213127777275 : ℚ) / 9679042368602776

def SurrogateDiagonalTailChunk000Sub000Block043Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1847
    = surrogateDiagTailX0RatChunk000Sub000Block043Part017

theorem surrogateDiagonalTailChunk000Sub000Block043Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part017] using hcert

def TailChunk000Sub000Block043Part018SupportExplicit : Finset ℕ :=
  ([1851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part018 : ℚ :=
  (2970497725 : ℚ) / 51434161895424

def SurrogateDiagonalTailChunk000Sub000Block043Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1851
    = surrogateDiagTailX0RatChunk000Sub000Block043Part018

theorem surrogateDiagonalTailChunk000Sub000Block043Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part018] using hcert

def TailChunk000Sub000Block043Part019SupportExplicit : Finset ℕ :=
  ([1853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part019 : ℚ :=
  (149070494875 : ℚ) / 5573677292716032

def SurrogateDiagonalTailChunk000Sub000Block043Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1853
    = surrogateDiagTailX0RatChunk000Sub000Block043Part019

theorem surrogateDiagonalTailChunk000Sub000Block043Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part019] using hcert

def TailChunk000Sub000Block043Part020SupportExplicit : Finset ℕ :=
  ([1855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part020 : ℚ :=
  (210319834325 : ℚ) / 3032879842197504

def SurrogateDiagonalTailChunk000Sub000Block043Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1855
    = surrogateDiagTailX0RatChunk000Sub000Block043Part020

theorem surrogateDiagonalTailChunk000Sub000Block043Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part020] using hcert

def TailChunk000Sub000Block043Part021SupportExplicit : Finset ℕ :=
  ([1857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part021 : ℚ :=
  (83713888375 : ℚ) / 1458951149643552

def SurrogateDiagonalTailChunk000Sub000Block043Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1857
    = surrogateDiagTailX0RatChunk000Sub000Block043Part021

theorem surrogateDiagonalTailChunk000Sub000Block043Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part021] using hcert

def TailChunk000Sub000Block043Part022SupportExplicit : Finset ℕ :=
  ([1858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part022 : ℚ :=
  (134742276125 : ℚ) / 927232761790464

def SurrogateDiagonalTailChunk000Sub000Block043Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1858
    = surrogateDiagTailX0RatChunk000Sub000Block043Part022

theorem surrogateDiagonalTailChunk000Sub000Block043Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part022] using hcert

def TailChunk000Sub000Block043Part023SupportExplicit : Finset ℕ :=
  ([1861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part023 : ℚ :=
  (2884946393 : ℚ) / 133013621404800

def SurrogateDiagonalTailChunk000Sub000Block043Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1861
    = surrogateDiagTailX0RatChunk000Sub000Block043Part023

theorem surrogateDiagonalTailChunk000Sub000Block043Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part023] using hcert

def TailChunk000Sub000Block043Part024SupportExplicit : Finset ℕ :=
  ([1865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block043Part024 : ℚ :=
  (186607089725 : ℚ) / 6129267674333184

def SurrogateDiagonalTailChunk000Sub000Block043Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1865
    = surrogateDiagTailX0RatChunk000Sub000Block043Part024

theorem surrogateDiagonalTailChunk000Sub000Block043Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block043Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block043Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block043Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block043Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block043Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block043HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block043Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block043Part000
    + surrogateDiagTailX0RatChunk000Sub000Block043Part001
    + surrogateDiagTailX0RatChunk000Sub000Block043Part002
    + surrogateDiagTailX0RatChunk000Sub000Block043Part003
    + surrogateDiagTailX0RatChunk000Sub000Block043Part004
    + surrogateDiagTailX0RatChunk000Sub000Block043Part005
    + surrogateDiagTailX0RatChunk000Sub000Block043Part006
    + surrogateDiagTailX0RatChunk000Sub000Block043Part007
    + surrogateDiagTailX0RatChunk000Sub000Block043Part008
    + surrogateDiagTailX0RatChunk000Sub000Block043Part009

def surrogateDiagonalTailChunk000Sub000Block043MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block043Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block043Part010
    + surrogateDiagTailX0RatChunk000Sub000Block043Part011
    + surrogateDiagTailX0RatChunk000Sub000Block043Part012
    + surrogateDiagTailX0RatChunk000Sub000Block043Part013
    + surrogateDiagTailX0RatChunk000Sub000Block043Part014
    + surrogateDiagTailX0RatChunk000Sub000Block043Part015
    + surrogateDiagTailX0RatChunk000Sub000Block043Part016
    + surrogateDiagTailX0RatChunk000Sub000Block043Part017
    + surrogateDiagTailX0RatChunk000Sub000Block043Part018
    + surrogateDiagTailX0RatChunk000Sub000Block043Part019

def surrogateDiagonalTailChunk000Sub000Block043TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block043Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block043Part020
    + surrogateDiagTailX0RatChunk000Sub000Block043Part021
    + surrogateDiagTailX0RatChunk000Sub000Block043Part022
    + surrogateDiagTailX0RatChunk000Sub000Block043Part023
    + surrogateDiagTailX0RatChunk000Sub000Block043Part024

def surrogateDiagonalTailChunk000Sub000Block043Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block043HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block043MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block043TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block043 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block043Part000
    + surrogateDiagTailX0RatChunk000Sub000Block043Part001
    + surrogateDiagTailX0RatChunk000Sub000Block043Part002
    + surrogateDiagTailX0RatChunk000Sub000Block043Part003
    + surrogateDiagTailX0RatChunk000Sub000Block043Part004
    + surrogateDiagTailX0RatChunk000Sub000Block043Part005
    + surrogateDiagTailX0RatChunk000Sub000Block043Part006
    + surrogateDiagTailX0RatChunk000Sub000Block043Part007
    + surrogateDiagTailX0RatChunk000Sub000Block043Part008
    + surrogateDiagTailX0RatChunk000Sub000Block043Part009
    + surrogateDiagTailX0RatChunk000Sub000Block043Part010
    + surrogateDiagTailX0RatChunk000Sub000Block043Part011
    + surrogateDiagTailX0RatChunk000Sub000Block043Part012
    + surrogateDiagTailX0RatChunk000Sub000Block043Part013
    + surrogateDiagTailX0RatChunk000Sub000Block043Part014
    + surrogateDiagTailX0RatChunk000Sub000Block043Part015
    + surrogateDiagTailX0RatChunk000Sub000Block043Part016
    + surrogateDiagTailX0RatChunk000Sub000Block043Part017
    + surrogateDiagTailX0RatChunk000Sub000Block043Part018
    + surrogateDiagTailX0RatChunk000Sub000Block043Part019
    + surrogateDiagTailX0RatChunk000Sub000Block043Part020
    + surrogateDiagTailX0RatChunk000Sub000Block043Part021
    + surrogateDiagTailX0RatChunk000Sub000Block043Part022
    + surrogateDiagTailX0RatChunk000Sub000Block043Part023
    + surrogateDiagTailX0RatChunk000Sub000Block043Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block043_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block043Head + surrogateDiagTailX0RatChunk000Sub000Block043Mid + surrogateDiagTailX0RatChunk000Sub000Block043Tail =
      surrogateDiagTailX0RatChunk000Sub000Block043 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block043Head surrogateDiagTailX0RatChunk000Sub000Block043Mid surrogateDiagTailX0RatChunk000Sub000Block043Tail surrogateDiagTailX0RatChunk000Sub000Block043
  ring

def SurrogateDiagonalTailChunk000Sub000Block043HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block043HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block043Head

def SurrogateDiagonalTailChunk000Sub000Block043MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block043MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block043Mid

def SurrogateDiagonalTailChunk000Sub000Block043TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block043TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block043Tail

theorem surrogateDiagonalTailChunk000Sub000Block043_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block043HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block043MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block043TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block043Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block043 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block043HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block043MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block043TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block043Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block043_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
