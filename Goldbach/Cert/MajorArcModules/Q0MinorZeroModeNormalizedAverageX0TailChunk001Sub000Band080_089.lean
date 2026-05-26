import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 000, blocks [80,90). -/

/-- Block 080 covers tail-support indices [12000,12025) and q from 19789 to 19826. -/

def TailChunk001Sub000Block080Part000SupportExplicit : Finset ℕ :=
  ([19789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part000 : ℚ :=
  (1188844181 : ℚ) / 123719797136424960

def SurrogateDiagonalTailChunk001Sub000Block080Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19789
    = surrogateDiagTailX0RatChunk001Sub000Block080Part000

theorem surrogateDiagonalTailChunk001Sub000Block080Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part000] using hcert

def TailChunk001Sub000Block080Part001SupportExplicit : Finset ℕ :=
  ([19790] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part001 : ℚ :=
  (1467826502475 : ℚ) / 3266259745379424256

def SurrogateDiagonalTailChunk001Sub000Block080Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19790
    = surrogateDiagTailX0RatChunk001Sub000Block080Part001

theorem surrogateDiagonalTailChunk001Sub000Block080Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part001] using hcert

def TailChunk001Sub000Block080Part002SupportExplicit : Finset ℕ :=
  ([19793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block080Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19793
    = surrogateDiagTailX0RatChunk001Sub000Block080Part002

theorem surrogateDiagonalTailChunk001Sub000Block080Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part002] using hcert

def TailChunk001Sub000Block080Part003SupportExplicit : Finset ℕ :=
  ([19794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part003 : ℚ :=
  (212510621575 : ℚ) / 295821315568667208

def SurrogateDiagonalTailChunk001Sub000Block080Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19794
    = surrogateDiagTailX0RatChunk001Sub000Block080Part003

theorem surrogateDiagonalTailChunk001Sub000Block080Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part003] using hcert

def TailChunk001Sub000Block080Part004SupportExplicit : Finset ℕ :=
  ([19795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part004 : ℚ :=
  (120236629625 : ℚ) / 15081959800516902912

def SurrogateDiagonalTailChunk001Sub000Block080Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19795
    = surrogateDiagTailX0RatChunk001Sub000Block080Part004

theorem surrogateDiagonalTailChunk001Sub000Block080Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part004] using hcert

def TailChunk001Sub000Block080Part005SupportExplicit : Finset ℕ :=
  ([19797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part005 : ℚ :=
  (1360737636275 : ℚ) / 37911074243285235264

def SurrogateDiagonalTailChunk001Sub000Block080Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19797
    = surrogateDiagTailX0RatChunk001Sub000Block080Part005

theorem surrogateDiagonalTailChunk001Sub000Block080Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part005] using hcert

def TailChunk001Sub000Block080Part006SupportExplicit : Finset ℕ :=
  ([19798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part006 : ℚ :=
  (14085381049 : ℚ) / 47981106878515200

def SurrogateDiagonalTailChunk001Sub000Block080Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19798
    = surrogateDiagTailX0RatChunk001Sub000Block080Part006

theorem surrogateDiagonalTailChunk001Sub000Block080Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part006] using hcert

def TailChunk001Sub000Block080Part007SupportExplicit : Finset ℕ :=
  ([19799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part007 : ℚ :=
  (27370017325 : ℚ) / 17389635147692661888

def SurrogateDiagonalTailChunk001Sub000Block080Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19799
    = surrogateDiagTailX0RatChunk001Sub000Block080Part007

theorem surrogateDiagonalTailChunk001Sub000Block080Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part007] using hcert

def TailChunk001Sub000Block080Part008SupportExplicit : Finset ℕ :=
  ([19801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block080Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19801
    = surrogateDiagTailX0RatChunk001Sub000Block080Part008

theorem surrogateDiagonalTailChunk001Sub000Block080Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part008] using hcert

def TailChunk001Sub000Block080Part009SupportExplicit : Finset ℕ :=
  ([19802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part009 : ℚ :=
  (98029801 : ℚ) / 384315251680800

def SurrogateDiagonalTailChunk001Sub000Block080Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19802
    = surrogateDiagTailX0RatChunk001Sub000Block080Part009

theorem surrogateDiagonalTailChunk001Sub000Block080Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part009] using hcert

def TailChunk001Sub000Block080Part010SupportExplicit : Finset ℕ :=
  ([19803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part010 : ℚ :=
  (24480240877 : ℚ) / 310944251038924800

def SurrogateDiagonalTailChunk001Sub000Block080Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19803
    = surrogateDiagTailX0RatChunk001Sub000Block080Part010

theorem surrogateDiagonalTailChunk001Sub000Block080Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part010] using hcert

def TailChunk001Sub000Block080Part011SupportExplicit : Finset ℕ :=
  ([19805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part011 : ℚ :=
  (576882580925 : ℚ) / 60767126276699848704

def SurrogateDiagonalTailChunk001Sub000Block080Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19805
    = surrogateDiagTailX0RatChunk001Sub000Block080Part011

theorem surrogateDiagonalTailChunk001Sub000Block080Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part011] using hcert

def TailChunk001Sub000Block080Part012SupportExplicit : Finset ℕ :=
  ([19806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part012 : ℚ :=
  (136250021 : ℚ) / 948926547360000

def SurrogateDiagonalTailChunk001Sub000Block080Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19806
    = surrogateDiagTailX0RatChunk001Sub000Block080Part012

theorem surrogateDiagonalTailChunk001Sub000Block080Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part012] using hcert

def TailChunk001Sub000Block080Part013SupportExplicit : Finset ℕ :=
  ([19807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part013 : ℚ :=
  (211979396425 : ℚ) / 332503700394767075328

def SurrogateDiagonalTailChunk001Sub000Block080Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19807
    = surrogateDiagTailX0RatChunk001Sub000Block080Part013

theorem surrogateDiagonalTailChunk001Sub000Block080Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part013] using hcert

def TailChunk001Sub000Block080Part014SupportExplicit : Finset ℕ :=
  ([19810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part014 : ℚ :=
  (83569042475 : ℚ) / 655810358444199936

def SurrogateDiagonalTailChunk001Sub000Block080Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19810
    = surrogateDiagTailX0RatChunk001Sub000Block080Part014

theorem surrogateDiagonalTailChunk001Sub000Block080Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part014] using hcert

def TailChunk001Sub000Block080Part015SupportExplicit : Finset ℕ :=
  ([19811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part015 : ℚ :=
  (24415374697 : ℚ) / 10499699520000000000

def SurrogateDiagonalTailChunk001Sub000Block080Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19811
    = surrogateDiagTailX0RatChunk001Sub000Block080Part015

theorem surrogateDiagonalTailChunk001Sub000Block080Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part015] using hcert

def TailChunk001Sub000Block080Part016SupportExplicit : Finset ℕ :=
  ([19813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block080Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19813
    = surrogateDiagTailX0RatChunk001Sub000Block080Part016

theorem surrogateDiagonalTailChunk001Sub000Block080Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part016] using hcert

def TailChunk001Sub000Block080Part017SupportExplicit : Finset ℕ :=
  ([19814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block080Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19814
    = surrogateDiagTailX0RatChunk001Sub000Block080Part017

theorem surrogateDiagonalTailChunk001Sub000Block080Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part017] using hcert

def TailChunk001Sub000Block080Part018SupportExplicit : Finset ℕ :=
  ([19815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part018 : ℚ :=
  (7994769071 : ℚ) / 103648083679641600

def SurrogateDiagonalTailChunk001Sub000Block080Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19815
    = surrogateDiagTailX0RatChunk001Sub000Block080Part018

theorem surrogateDiagonalTailChunk001Sub000Block080Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part018] using hcert

def TailChunk001Sub000Block080Part019SupportExplicit : Finset ℕ :=
  ([19817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part019 : ℚ :=
  (1203597320575 : ℚ) / 163218259509280800768

def SurrogateDiagonalTailChunk001Sub000Block080Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19817
    = surrogateDiagTailX0RatChunk001Sub000Block080Part019

theorem surrogateDiagonalTailChunk001Sub000Block080Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part019] using hcert

def TailChunk001Sub000Block080Part020SupportExplicit : Finset ℕ :=
  ([19819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block080Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19819
    = surrogateDiagTailX0RatChunk001Sub000Block080Part020

theorem surrogateDiagonalTailChunk001Sub000Block080Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part020] using hcert

def TailChunk001Sub000Block080Part021SupportExplicit : Finset ℕ :=
  ([19821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part021 : ℚ :=
  (1364038636175 : ℚ) / 38095275904948574784

def SurrogateDiagonalTailChunk001Sub000Block080Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19821
    = surrogateDiagTailX0RatChunk001Sub000Block080Part021

theorem surrogateDiagonalTailChunk001Sub000Block080Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part021] using hcert

def TailChunk001Sub000Block080Part022SupportExplicit : Finset ℕ :=
  ([19822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part022 : ℚ :=
  (19006205077 : ℚ) / 479269900989235200

def SurrogateDiagonalTailChunk001Sub000Block080Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19822
    = surrogateDiagTailX0RatChunk001Sub000Block080Part022

theorem surrogateDiagonalTailChunk001Sub000Block080Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part022] using hcert

def TailChunk001Sub000Block080Part023SupportExplicit : Finset ℕ :=
  ([19823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part023 : ℚ :=
  (633541183 : ℚ) / 1393526842176107520

def SurrogateDiagonalTailChunk001Sub000Block080Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19823
    = surrogateDiagTailX0RatChunk001Sub000Block080Part023

theorem surrogateDiagonalTailChunk001Sub000Block080Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part023] using hcert

def TailChunk001Sub000Block080Part024SupportExplicit : Finset ℕ :=
  ([19826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block080Part024 : ℚ :=
  (178304439 : ℚ) / 26701160732847040

def SurrogateDiagonalTailChunk001Sub000Block080Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19826
    = surrogateDiagTailX0RatChunk001Sub000Block080Part024

theorem surrogateDiagonalTailChunk001Sub000Block080Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block080Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block080Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block080Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block080Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block080Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block080HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block080Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block080Part000
    + surrogateDiagTailX0RatChunk001Sub000Block080Part001
    + surrogateDiagTailX0RatChunk001Sub000Block080Part002
    + surrogateDiagTailX0RatChunk001Sub000Block080Part003
    + surrogateDiagTailX0RatChunk001Sub000Block080Part004
    + surrogateDiagTailX0RatChunk001Sub000Block080Part005
    + surrogateDiagTailX0RatChunk001Sub000Block080Part006
    + surrogateDiagTailX0RatChunk001Sub000Block080Part007
    + surrogateDiagTailX0RatChunk001Sub000Block080Part008
    + surrogateDiagTailX0RatChunk001Sub000Block080Part009

def surrogateDiagonalTailChunk001Sub000Block080MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block080Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block080Part010
    + surrogateDiagTailX0RatChunk001Sub000Block080Part011
    + surrogateDiagTailX0RatChunk001Sub000Block080Part012
    + surrogateDiagTailX0RatChunk001Sub000Block080Part013
    + surrogateDiagTailX0RatChunk001Sub000Block080Part014
    + surrogateDiagTailX0RatChunk001Sub000Block080Part015
    + surrogateDiagTailX0RatChunk001Sub000Block080Part016
    + surrogateDiagTailX0RatChunk001Sub000Block080Part017
    + surrogateDiagTailX0RatChunk001Sub000Block080Part018
    + surrogateDiagTailX0RatChunk001Sub000Block080Part019

def surrogateDiagonalTailChunk001Sub000Block080TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block080Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block080Part020
    + surrogateDiagTailX0RatChunk001Sub000Block080Part021
    + surrogateDiagTailX0RatChunk001Sub000Block080Part022
    + surrogateDiagTailX0RatChunk001Sub000Block080Part023
    + surrogateDiagTailX0RatChunk001Sub000Block080Part024

def surrogateDiagonalTailChunk001Sub000Block080Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block080HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block080MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block080TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block080 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block080Part000
    + surrogateDiagTailX0RatChunk001Sub000Block080Part001
    + surrogateDiagTailX0RatChunk001Sub000Block080Part002
    + surrogateDiagTailX0RatChunk001Sub000Block080Part003
    + surrogateDiagTailX0RatChunk001Sub000Block080Part004
    + surrogateDiagTailX0RatChunk001Sub000Block080Part005
    + surrogateDiagTailX0RatChunk001Sub000Block080Part006
    + surrogateDiagTailX0RatChunk001Sub000Block080Part007
    + surrogateDiagTailX0RatChunk001Sub000Block080Part008
    + surrogateDiagTailX0RatChunk001Sub000Block080Part009
    + surrogateDiagTailX0RatChunk001Sub000Block080Part010
    + surrogateDiagTailX0RatChunk001Sub000Block080Part011
    + surrogateDiagTailX0RatChunk001Sub000Block080Part012
    + surrogateDiagTailX0RatChunk001Sub000Block080Part013
    + surrogateDiagTailX0RatChunk001Sub000Block080Part014
    + surrogateDiagTailX0RatChunk001Sub000Block080Part015
    + surrogateDiagTailX0RatChunk001Sub000Block080Part016
    + surrogateDiagTailX0RatChunk001Sub000Block080Part017
    + surrogateDiagTailX0RatChunk001Sub000Block080Part018
    + surrogateDiagTailX0RatChunk001Sub000Block080Part019
    + surrogateDiagTailX0RatChunk001Sub000Block080Part020
    + surrogateDiagTailX0RatChunk001Sub000Block080Part021
    + surrogateDiagTailX0RatChunk001Sub000Block080Part022
    + surrogateDiagTailX0RatChunk001Sub000Block080Part023
    + surrogateDiagTailX0RatChunk001Sub000Block080Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block080_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block080Head + surrogateDiagTailX0RatChunk001Sub000Block080Mid + surrogateDiagTailX0RatChunk001Sub000Block080Tail =
      surrogateDiagTailX0RatChunk001Sub000Block080 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block080Head surrogateDiagTailX0RatChunk001Sub000Block080Mid surrogateDiagTailX0RatChunk001Sub000Block080Tail surrogateDiagTailX0RatChunk001Sub000Block080
  ring

def SurrogateDiagonalTailChunk001Sub000Block080HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block080HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block080Head

def SurrogateDiagonalTailChunk001Sub000Block080MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block080MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block080Mid

def SurrogateDiagonalTailChunk001Sub000Block080TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block080TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block080Tail

theorem surrogateDiagonalTailChunk001Sub000Block080_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block080HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block080MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block080TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block080Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block080 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block080HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block080MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block080TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block080Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block080_eq_head_add_mid_add_tail

/-- Block 081 covers tail-support indices [12025,12050) and q from 19829 to 19867. -/

def TailChunk001Sub000Block081Part000SupportExplicit : Finset ℕ :=
  ([19829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part000 : ℚ :=
  (3928807843 : ℚ) / 14461898051250000000

def SurrogateDiagonalTailChunk001Sub000Block081Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19829
    = surrogateDiagTailX0RatChunk001Sub000Block081Part000

theorem surrogateDiagonalTailChunk001Sub000Block081Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part000] using hcert

def TailChunk001Sub000Block081Part001SupportExplicit : Finset ℕ :=
  ([19830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part001 : ℚ :=
  (10198194803 : ℚ) / 25912020919910400

def SurrogateDiagonalTailChunk001Sub000Block081Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19830
    = surrogateDiagTailX0RatChunk001Sub000Block081Part001

theorem surrogateDiagonalTailChunk001Sub000Block081Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part001] using hcert

def TailChunk001Sub000Block081Part002SupportExplicit : Finset ℕ :=
  ([19831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part002 : ℚ :=
  (502101161675 : ℚ) / 104225709650220417024

def SurrogateDiagonalTailChunk001Sub000Block081Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19831
    = surrogateDiagTailX0RatChunk001Sub000Block081Part002

theorem surrogateDiagonalTailChunk001Sub000Block081Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part002] using hcert

def TailChunk001Sub000Block081Part003SupportExplicit : Finset ℕ :=
  ([19833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part003 : ℚ :=
  (21109873919 : ℚ) / 414802944000000000

def SurrogateDiagonalTailChunk001Sub000Block081Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19833
    = surrogateDiagTailX0RatChunk001Sub000Block081Part003

theorem surrogateDiagonalTailChunk001Sub000Block081Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part003] using hcert

def TailChunk001Sub000Block081Part004SupportExplicit : Finset ℕ :=
  ([19834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part004 : ℚ :=
  (3206835271 : ℚ) / 870954276360067200

def SurrogateDiagonalTailChunk001Sub000Block081Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19834
    = surrogateDiagTailX0RatChunk001Sub000Block081Part004

theorem surrogateDiagonalTailChunk001Sub000Block081Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part004] using hcert

def TailChunk001Sub000Block081Part005SupportExplicit : Finset ℕ :=
  ([19835] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part005 : ℚ :=
  (984322941625 : ℚ) / 158371731034899499008

def SurrogateDiagonalTailChunk001Sub000Block081Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19835
    = surrogateDiagTailX0RatChunk001Sub000Block081Part005

theorem surrogateDiagonalTailChunk001Sub000Block081Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part005] using hcert

def TailChunk001Sub000Block081Part006SupportExplicit : Finset ℕ :=
  ([19837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part006 : ℚ :=
  (12007965875 : ℚ) / 45341941226040702096

def SurrogateDiagonalTailChunk001Sub000Block081Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19837
    = surrogateDiagTailX0RatChunk001Sub000Block081Part006

theorem surrogateDiagonalTailChunk001Sub000Block081Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part006] using hcert

def TailChunk001Sub000Block081Part007SupportExplicit : Finset ℕ :=
  ([19838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part007 : ℚ :=
  (1287783875 : ℚ) / 18811160862916608

def SurrogateDiagonalTailChunk001Sub000Block081Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19838
    = surrogateDiagTailX0RatChunk001Sub000Block081Part007

theorem surrogateDiagonalTailChunk001Sub000Block081Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part007] using hcert

def TailChunk001Sub000Block081Part008SupportExplicit : Finset ℕ :=
  ([19839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part008 : ℚ :=
  (2644543547575 : ℚ) / 59422876985425133568

def SurrogateDiagonalTailChunk001Sub000Block081Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19839
    = surrogateDiagTailX0RatChunk001Sub000Block081Part008

theorem surrogateDiagonalTailChunk001Sub000Block081Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part008] using hcert

def TailChunk001Sub000Block081Part009SupportExplicit : Finset ℕ :=
  ([19841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19841
    = surrogateDiagTailX0RatChunk001Sub000Block081Part009

theorem surrogateDiagonalTailChunk001Sub000Block081Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part009] using hcert

def TailChunk001Sub000Block081Part010SupportExplicit : Finset ℕ :=
  ([19842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part010 : ℚ :=
  (341863677425 : ℚ) / 2389616689622289984

def SurrogateDiagonalTailChunk001Sub000Block081Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19842
    = surrogateDiagTailX0RatChunk001Sub000Block081Part010

theorem surrogateDiagonalTailChunk001Sub000Block081Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part010] using hcert

def TailChunk001Sub000Block081Part011SupportExplicit : Finset ℕ :=
  ([19843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19843
    = surrogateDiagTailX0RatChunk001Sub000Block081Part011

theorem surrogateDiagonalTailChunk001Sub000Block081Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part011] using hcert

def TailChunk001Sub000Block081Part012SupportExplicit : Finset ℕ :=
  ([19846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19846
    = surrogateDiagTailX0RatChunk001Sub000Block081Part012

theorem surrogateDiagonalTailChunk001Sub000Block081Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part012] using hcert

def TailChunk001Sub000Block081Part013SupportExplicit : Finset ℕ :=
  ([19847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part013 : ℚ :=
  (95370501175 : ℚ) / 364224742794601463808

def SurrogateDiagonalTailChunk001Sub000Block081Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19847
    = surrogateDiagTailX0RatChunk001Sub000Block081Part013

theorem surrogateDiagonalTailChunk001Sub000Block081Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part013] using hcert

def TailChunk001Sub000Block081Part014SupportExplicit : Finset ℕ :=
  ([19849] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part014 : ℚ :=
  (285227623075 : ℚ) / 323404937033354951808

def SurrogateDiagonalTailChunk001Sub000Block081Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19849
    = surrogateDiagTailX0RatChunk001Sub000Block081Part014

theorem surrogateDiagonalTailChunk001Sub000Block081Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part014] using hcert

def TailChunk001Sub000Block081Part015SupportExplicit : Finset ℕ :=
  ([19851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part015 : ℚ :=
  (2620445651875 : ℚ) / 55249286631743029248

def SurrogateDiagonalTailChunk001Sub000Block081Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19851
    = surrogateDiagTailX0RatChunk001Sub000Block081Part015

theorem surrogateDiagonalTailChunk001Sub000Block081Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part015] using hcert

def TailChunk001Sub000Block081Part016SupportExplicit : Finset ℕ :=
  ([19853] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19853
    = surrogateDiagTailX0RatChunk001Sub000Block081Part016

theorem surrogateDiagonalTailChunk001Sub000Block081Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part016] using hcert

def TailChunk001Sub000Block081Part017SupportExplicit : Finset ℕ :=
  ([19857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part017 : ℚ :=
  (1368997636025 : ℚ) / 38372835966782359104

def SurrogateDiagonalTailChunk001Sub000Block081Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19857
    = surrogateDiagTailX0RatChunk001Sub000Block081Part017

theorem surrogateDiagonalTailChunk001Sub000Block081Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part017] using hcert

def TailChunk001Sub000Block081Part018SupportExplicit : Finset ℕ :=
  ([19858] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19858
    = surrogateDiagTailX0RatChunk001Sub000Block081Part018

theorem surrogateDiagonalTailChunk001Sub000Block081Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part018] using hcert

def TailChunk001Sub000Block081Part019SupportExplicit : Finset ℕ :=
  ([19859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part019 : ℚ :=
  (503517878375 : ℚ) / 104815804197287568384

def SurrogateDiagonalTailChunk001Sub000Block081Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19859
    = surrogateDiagTailX0RatChunk001Sub000Block081Part019

theorem surrogateDiagonalTailChunk001Sub000Block081Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part019] using hcert

def TailChunk001Sub000Block081Part020SupportExplicit : Finset ℕ :=
  ([19861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19861
    = surrogateDiagTailX0RatChunk001Sub000Block081Part020

theorem surrogateDiagonalTailChunk001Sub000Block081Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part020] using hcert

def TailChunk001Sub000Block081Part021SupportExplicit : Finset ℕ :=
  ([19862] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19862
    = surrogateDiagTailX0RatChunk001Sub000Block081Part021

theorem surrogateDiagonalTailChunk001Sub000Block081Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part021] using hcert

def TailChunk001Sub000Block081Part022SupportExplicit : Finset ℕ :=
  ([19865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part022 : ℚ :=
  (675283953675 : ℚ) / 44867650508340330496

def SurrogateDiagonalTailChunk001Sub000Block081Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19865
    = surrogateDiagTailX0RatChunk001Sub000Block081Part022

theorem surrogateDiagonalTailChunk001Sub000Block081Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part022] using hcert

def TailChunk001Sub000Block081Part023SupportExplicit : Finset ℕ :=
  ([19866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part023 : ℚ :=
  (1567455689 : ℚ) / 3226851654082560

def SurrogateDiagonalTailChunk001Sub000Block081Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19866
    = surrogateDiagTailX0RatChunk001Sub000Block081Part023

theorem surrogateDiagonalTailChunk001Sub000Block081Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part023] using hcert

def TailChunk001Sub000Block081Part024SupportExplicit : Finset ℕ :=
  ([19867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block081Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block081Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19867
    = surrogateDiagTailX0RatChunk001Sub000Block081Part024

theorem surrogateDiagonalTailChunk001Sub000Block081Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block081Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block081Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block081Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block081Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block081Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block081HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block081Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block081Part000
    + surrogateDiagTailX0RatChunk001Sub000Block081Part001
    + surrogateDiagTailX0RatChunk001Sub000Block081Part002
    + surrogateDiagTailX0RatChunk001Sub000Block081Part003
    + surrogateDiagTailX0RatChunk001Sub000Block081Part004
    + surrogateDiagTailX0RatChunk001Sub000Block081Part005
    + surrogateDiagTailX0RatChunk001Sub000Block081Part006
    + surrogateDiagTailX0RatChunk001Sub000Block081Part007
    + surrogateDiagTailX0RatChunk001Sub000Block081Part008
    + surrogateDiagTailX0RatChunk001Sub000Block081Part009

def surrogateDiagonalTailChunk001Sub000Block081MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block081Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block081Part010
    + surrogateDiagTailX0RatChunk001Sub000Block081Part011
    + surrogateDiagTailX0RatChunk001Sub000Block081Part012
    + surrogateDiagTailX0RatChunk001Sub000Block081Part013
    + surrogateDiagTailX0RatChunk001Sub000Block081Part014
    + surrogateDiagTailX0RatChunk001Sub000Block081Part015
    + surrogateDiagTailX0RatChunk001Sub000Block081Part016
    + surrogateDiagTailX0RatChunk001Sub000Block081Part017
    + surrogateDiagTailX0RatChunk001Sub000Block081Part018
    + surrogateDiagTailX0RatChunk001Sub000Block081Part019

def surrogateDiagonalTailChunk001Sub000Block081TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block081Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block081Part020
    + surrogateDiagTailX0RatChunk001Sub000Block081Part021
    + surrogateDiagTailX0RatChunk001Sub000Block081Part022
    + surrogateDiagTailX0RatChunk001Sub000Block081Part023
    + surrogateDiagTailX0RatChunk001Sub000Block081Part024

def surrogateDiagonalTailChunk001Sub000Block081Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block081HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block081MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block081TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block081 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block081Part000
    + surrogateDiagTailX0RatChunk001Sub000Block081Part001
    + surrogateDiagTailX0RatChunk001Sub000Block081Part002
    + surrogateDiagTailX0RatChunk001Sub000Block081Part003
    + surrogateDiagTailX0RatChunk001Sub000Block081Part004
    + surrogateDiagTailX0RatChunk001Sub000Block081Part005
    + surrogateDiagTailX0RatChunk001Sub000Block081Part006
    + surrogateDiagTailX0RatChunk001Sub000Block081Part007
    + surrogateDiagTailX0RatChunk001Sub000Block081Part008
    + surrogateDiagTailX0RatChunk001Sub000Block081Part009
    + surrogateDiagTailX0RatChunk001Sub000Block081Part010
    + surrogateDiagTailX0RatChunk001Sub000Block081Part011
    + surrogateDiagTailX0RatChunk001Sub000Block081Part012
    + surrogateDiagTailX0RatChunk001Sub000Block081Part013
    + surrogateDiagTailX0RatChunk001Sub000Block081Part014
    + surrogateDiagTailX0RatChunk001Sub000Block081Part015
    + surrogateDiagTailX0RatChunk001Sub000Block081Part016
    + surrogateDiagTailX0RatChunk001Sub000Block081Part017
    + surrogateDiagTailX0RatChunk001Sub000Block081Part018
    + surrogateDiagTailX0RatChunk001Sub000Block081Part019
    + surrogateDiagTailX0RatChunk001Sub000Block081Part020
    + surrogateDiagTailX0RatChunk001Sub000Block081Part021
    + surrogateDiagTailX0RatChunk001Sub000Block081Part022
    + surrogateDiagTailX0RatChunk001Sub000Block081Part023
    + surrogateDiagTailX0RatChunk001Sub000Block081Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block081_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block081Head + surrogateDiagTailX0RatChunk001Sub000Block081Mid + surrogateDiagTailX0RatChunk001Sub000Block081Tail =
      surrogateDiagTailX0RatChunk001Sub000Block081 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block081Head surrogateDiagTailX0RatChunk001Sub000Block081Mid surrogateDiagTailX0RatChunk001Sub000Block081Tail surrogateDiagTailX0RatChunk001Sub000Block081
  ring

def SurrogateDiagonalTailChunk001Sub000Block081HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block081HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block081Head

def SurrogateDiagonalTailChunk001Sub000Block081MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block081MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block081Mid

def SurrogateDiagonalTailChunk001Sub000Block081TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block081TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block081Tail

theorem surrogateDiagonalTailChunk001Sub000Block081_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block081HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block081MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block081TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block081Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block081 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block081HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block081MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block081TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block081Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block081_eq_head_add_mid_add_tail

/-- Block 082 covers tail-support indices [12050,12075) and q from 19869 to 19907. -/

def TailChunk001Sub000Block082Part000SupportExplicit : Finset ℕ :=
  ([19869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part000 : ℚ :=
  (299527939675 : ℚ) / 7495391888627761152

def SurrogateDiagonalTailChunk001Sub000Block082Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19869
    = surrogateDiagTailX0RatChunk001Sub000Block082Part000

theorem surrogateDiagonalTailChunk001Sub000Block082Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part000] using hcert

def TailChunk001Sub000Block082Part001SupportExplicit : Finset ℕ :=
  ([19870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part001 : ℚ :=
  (185122738675 : ℚ) / 2489566947653325312

def SurrogateDiagonalTailChunk001Sub000Block082Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19870
    = surrogateDiagTailX0RatChunk001Sub000Block082Part001

theorem surrogateDiagonalTailChunk001Sub000Block082Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part001] using hcert

def TailChunk001Sub000Block082Part002SupportExplicit : Finset ℕ :=
  ([19871] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part002 : ℚ :=
  (3766909601 : ℚ) / 6796131434496000000

def SurrogateDiagonalTailChunk001Sub000Block082Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19871
    = surrogateDiagTailX0RatChunk001Sub000Block082Part002

theorem surrogateDiagonalTailChunk001Sub000Block082Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part002] using hcert

def TailChunk001Sub000Block082Part003SupportExplicit : Finset ℕ :=
  ([19873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part003 : ℚ :=
  (760258281325 : ℚ) / 161266493588250820608

def SurrogateDiagonalTailChunk001Sub000Block082Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19873
    = surrogateDiagTailX0RatChunk001Sub000Block082Part003

theorem surrogateDiagonalTailChunk001Sub000Block082Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part003] using hcert

def TailChunk001Sub000Block082Part004SupportExplicit : Finset ℕ :=
  ([19874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part004 : ℚ :=
  (9915553975 : ℚ) / 1218088684047044808

def SurrogateDiagonalTailChunk001Sub000Block082Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19874
    = surrogateDiagTailX0RatChunk001Sub000Block082Part004

theorem surrogateDiagonalTailChunk001Sub000Block082Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part004] using hcert

def TailChunk001Sub000Block082Part005SupportExplicit : Finset ℕ :=
  ([19877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part005 : ℚ :=
  (37773460681 : ℚ) / 7521910818243379200

def SurrogateDiagonalTailChunk001Sub000Block082Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19877
    = surrogateDiagTailX0RatChunk001Sub000Block082Part005

theorem surrogateDiagonalTailChunk001Sub000Block082Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part005] using hcert

def TailChunk001Sub000Block082Part006SupportExplicit : Finset ℕ :=
  ([19878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part006 : ℚ :=
  (685759280075 : ℚ) / 2407011461837881344

def SurrogateDiagonalTailChunk001Sub000Block082Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19878
    = surrogateDiagTailX0RatChunk001Sub000Block082Part006

theorem surrogateDiagonalTailChunk001Sub000Block082Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part006] using hcert

def TailChunk001Sub000Block082Part007SupportExplicit : Finset ℕ :=
  ([19879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part007 : ℚ :=
  (91134578275 : ℚ) / 367817561414270189568

def SurrogateDiagonalTailChunk001Sub000Block082Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19879
    = surrogateDiagTailX0RatChunk001Sub000Block082Part007

theorem surrogateDiagonalTailChunk001Sub000Block082Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part007] using hcert

def TailChunk001Sub000Block082Part008SupportExplicit : Finset ℕ :=
  ([19882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block082Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19882
    = surrogateDiagTailX0RatChunk001Sub000Block082Part008

theorem surrogateDiagonalTailChunk001Sub000Block082Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part008] using hcert

def TailChunk001Sub000Block082Part009SupportExplicit : Finset ℕ :=
  ([19883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part009 : ℚ :=
  (4418613625 : ℚ) / 12880653910412230656

def SurrogateDiagonalTailChunk001Sub000Block082Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19883
    = surrogateDiagTailX0RatChunk001Sub000Block082Part009

theorem surrogateDiagonalTailChunk001Sub000Block082Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part009] using hcert

def TailChunk001Sub000Block082Part010SupportExplicit : Finset ℕ :=
  ([19885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part010 : ℚ :=
  (584172707 : ℚ) / 74231878281854976

def SurrogateDiagonalTailChunk001Sub000Block082Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19885
    = surrogateDiagTailX0RatChunk001Sub000Block082Part010

theorem surrogateDiagonalTailChunk001Sub000Block082Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part010] using hcert

def TailChunk001Sub000Block082Part011SupportExplicit : Finset ℕ :=
  ([19886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part011 : ℚ :=
  (346489421 : ℚ) / 111599416252166400

def SurrogateDiagonalTailChunk001Sub000Block082Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19886
    = surrogateDiagTailX0RatChunk001Sub000Block082Part011

theorem surrogateDiagonalTailChunk001Sub000Block082Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part011] using hcert

def TailChunk001Sub000Block082Part012SupportExplicit : Finset ℕ :=
  ([19887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part012 : ℚ :=
  (239321718575 : ℚ) / 3775058651974883328

def SurrogateDiagonalTailChunk001Sub000Block082Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19887
    = surrogateDiagTailX0RatChunk001Sub000Block082Part012

theorem surrogateDiagonalTailChunk001Sub000Block082Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part012] using hcert

def TailChunk001Sub000Block082Part013SupportExplicit : Finset ℕ :=
  ([19889] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block082Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19889
    = surrogateDiagTailX0RatChunk001Sub000Block082Part013

theorem surrogateDiagonalTailChunk001Sub000Block082Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part013] using hcert

def TailChunk001Sub000Block082Part014SupportExplicit : Finset ℕ :=
  ([19891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block082Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19891
    = surrogateDiagTailX0RatChunk001Sub000Block082Part014

theorem surrogateDiagonalTailChunk001Sub000Block082Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part014] using hcert

def TailChunk001Sub000Block082Part015SupportExplicit : Finset ℕ :=
  ([19893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part015 : ℚ :=
  (33030280475 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk001Sub000Block082Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19893
    = surrogateDiagTailX0RatChunk001Sub000Block082Part015

theorem surrogateDiagonalTailChunk001Sub000Block082Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part015] using hcert

def TailChunk001Sub000Block082Part016SupportExplicit : Finset ℕ :=
  ([19895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part016 : ℚ :=
  (556566955775 : ℚ) / 65620772617044885504

def SurrogateDiagonalTailChunk001Sub000Block082Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19895
    = surrogateDiagTailX0RatChunk001Sub000Block082Part016

theorem surrogateDiagonalTailChunk001Sub000Block082Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part016] using hcert

def TailChunk001Sub000Block082Part017SupportExplicit : Finset ℕ :=
  ([19897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part017 : ℚ :=
  (48689031 : ℚ) / 196811228508160000

def SurrogateDiagonalTailChunk001Sub000Block082Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19897
    = surrogateDiagTailX0RatChunk001Sub000Block082Part017

theorem surrogateDiagonalTailChunk001Sub000Block082Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part017] using hcert

def TailChunk001Sub000Block082Part018SupportExplicit : Finset ℕ :=
  ([19898] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block082Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19898
    = surrogateDiagTailX0RatChunk001Sub000Block082Part018

theorem surrogateDiagonalTailChunk001Sub000Block082Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part018] using hcert

def TailChunk001Sub000Block082Part019SupportExplicit : Finset ℕ :=
  ([19901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part019 : ℚ :=
  (505646702675 : ℚ) / 105705639781395683904

def SurrogateDiagonalTailChunk001Sub000Block082Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19901
    = surrogateDiagTailX0RatChunk001Sub000Block082Part019

theorem surrogateDiagonalTailChunk001Sub000Block082Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part019] using hcert

def TailChunk001Sub000Block082Part020SupportExplicit : Finset ℕ :=
  ([19902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part020 : ℚ :=
  (2156337565 : ℚ) / 6545989496752128

def SurrogateDiagonalTailChunk001Sub000Block082Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19902
    = surrogateDiagTailX0RatChunk001Sub000Block082Part020

theorem surrogateDiagonalTailChunk001Sub000Block082Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part020] using hcert

def TailChunk001Sub000Block082Part021SupportExplicit : Finset ℕ :=
  ([19903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part021 : ℚ :=
  (2212482209 : ℚ) / 1420651553848070400

def SurrogateDiagonalTailChunk001Sub000Block082Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19903
    = surrogateDiagTailX0RatChunk001Sub000Block082Part021

theorem surrogateDiagonalTailChunk001Sub000Block082Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part021] using hcert

def TailChunk001Sub000Block082Part022SupportExplicit : Finset ℕ :=
  ([19905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part022 : ℚ :=
  (50422112825 : ℚ) / 659659263802546176

def SurrogateDiagonalTailChunk001Sub000Block082Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19905
    = surrogateDiagTailX0RatChunk001Sub000Block082Part022

theorem surrogateDiagonalTailChunk001Sub000Block082Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part022] using hcert

def TailChunk001Sub000Block082Part023SupportExplicit : Finset ℕ :=
  ([19906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part023 : ℚ :=
  (1436156425 : ℚ) / 323371123377537024

def SurrogateDiagonalTailChunk001Sub000Block082Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19906
    = surrogateDiagTailX0RatChunk001Sub000Block082Part023

theorem surrogateDiagonalTailChunk001Sub000Block082Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part023] using hcert

def TailChunk001Sub000Block082Part024SupportExplicit : Finset ℕ :=
  ([19907] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block082Part024 : ℚ :=
  (17297504281 : ℚ) / 12283163360899891200

def SurrogateDiagonalTailChunk001Sub000Block082Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19907
    = surrogateDiagTailX0RatChunk001Sub000Block082Part024

theorem surrogateDiagonalTailChunk001Sub000Block082Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block082Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block082Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block082Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block082Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block082Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block082HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block082Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block082Part000
    + surrogateDiagTailX0RatChunk001Sub000Block082Part001
    + surrogateDiagTailX0RatChunk001Sub000Block082Part002
    + surrogateDiagTailX0RatChunk001Sub000Block082Part003
    + surrogateDiagTailX0RatChunk001Sub000Block082Part004
    + surrogateDiagTailX0RatChunk001Sub000Block082Part005
    + surrogateDiagTailX0RatChunk001Sub000Block082Part006
    + surrogateDiagTailX0RatChunk001Sub000Block082Part007
    + surrogateDiagTailX0RatChunk001Sub000Block082Part008
    + surrogateDiagTailX0RatChunk001Sub000Block082Part009

def surrogateDiagonalTailChunk001Sub000Block082MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block082Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block082Part010
    + surrogateDiagTailX0RatChunk001Sub000Block082Part011
    + surrogateDiagTailX0RatChunk001Sub000Block082Part012
    + surrogateDiagTailX0RatChunk001Sub000Block082Part013
    + surrogateDiagTailX0RatChunk001Sub000Block082Part014
    + surrogateDiagTailX0RatChunk001Sub000Block082Part015
    + surrogateDiagTailX0RatChunk001Sub000Block082Part016
    + surrogateDiagTailX0RatChunk001Sub000Block082Part017
    + surrogateDiagTailX0RatChunk001Sub000Block082Part018
    + surrogateDiagTailX0RatChunk001Sub000Block082Part019

def surrogateDiagonalTailChunk001Sub000Block082TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block082Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block082Part020
    + surrogateDiagTailX0RatChunk001Sub000Block082Part021
    + surrogateDiagTailX0RatChunk001Sub000Block082Part022
    + surrogateDiagTailX0RatChunk001Sub000Block082Part023
    + surrogateDiagTailX0RatChunk001Sub000Block082Part024

def surrogateDiagonalTailChunk001Sub000Block082Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block082HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block082MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block082TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block082 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block082Part000
    + surrogateDiagTailX0RatChunk001Sub000Block082Part001
    + surrogateDiagTailX0RatChunk001Sub000Block082Part002
    + surrogateDiagTailX0RatChunk001Sub000Block082Part003
    + surrogateDiagTailX0RatChunk001Sub000Block082Part004
    + surrogateDiagTailX0RatChunk001Sub000Block082Part005
    + surrogateDiagTailX0RatChunk001Sub000Block082Part006
    + surrogateDiagTailX0RatChunk001Sub000Block082Part007
    + surrogateDiagTailX0RatChunk001Sub000Block082Part008
    + surrogateDiagTailX0RatChunk001Sub000Block082Part009
    + surrogateDiagTailX0RatChunk001Sub000Block082Part010
    + surrogateDiagTailX0RatChunk001Sub000Block082Part011
    + surrogateDiagTailX0RatChunk001Sub000Block082Part012
    + surrogateDiagTailX0RatChunk001Sub000Block082Part013
    + surrogateDiagTailX0RatChunk001Sub000Block082Part014
    + surrogateDiagTailX0RatChunk001Sub000Block082Part015
    + surrogateDiagTailX0RatChunk001Sub000Block082Part016
    + surrogateDiagTailX0RatChunk001Sub000Block082Part017
    + surrogateDiagTailX0RatChunk001Sub000Block082Part018
    + surrogateDiagTailX0RatChunk001Sub000Block082Part019
    + surrogateDiagTailX0RatChunk001Sub000Block082Part020
    + surrogateDiagTailX0RatChunk001Sub000Block082Part021
    + surrogateDiagTailX0RatChunk001Sub000Block082Part022
    + surrogateDiagTailX0RatChunk001Sub000Block082Part023
    + surrogateDiagTailX0RatChunk001Sub000Block082Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block082_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block082Head + surrogateDiagTailX0RatChunk001Sub000Block082Mid + surrogateDiagTailX0RatChunk001Sub000Block082Tail =
      surrogateDiagTailX0RatChunk001Sub000Block082 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block082Head surrogateDiagTailX0RatChunk001Sub000Block082Mid surrogateDiagTailX0RatChunk001Sub000Block082Tail surrogateDiagTailX0RatChunk001Sub000Block082
  ring

def SurrogateDiagonalTailChunk001Sub000Block082HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block082HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block082Head

def SurrogateDiagonalTailChunk001Sub000Block082MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block082MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block082Mid

def SurrogateDiagonalTailChunk001Sub000Block082TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block082TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block082Tail

theorem surrogateDiagonalTailChunk001Sub000Block082_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block082HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block082MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block082TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block082Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block082 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block082HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block082MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block082TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block082Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block082_eq_head_add_mid_add_tail

/-- Block 083 covers tail-support indices [12075,12100) and q from 19909 to 19951. -/

def TailChunk001Sub000Block083Part000SupportExplicit : Finset ℕ :=
  ([19909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part000 : ℚ :=
  (3628420175 : ℚ) / 8056367080744463712

def SurrogateDiagonalTailChunk001Sub000Block083Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19909
    = surrogateDiagTailX0RatChunk001Sub000Block083Part000

theorem surrogateDiagonalTailChunk001Sub000Block083Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part000] using hcert

def TailChunk001Sub000Block083Part001SupportExplicit : Finset ℕ :=
  ([19910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part001 : ℚ :=
  (1304575067 : ℚ) / 13439615385600000

def SurrogateDiagonalTailChunk001Sub000Block083Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19910
    = surrogateDiagTailX0RatChunk001Sub000Block083Part001

theorem surrogateDiagonalTailChunk001Sub000Block083Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part001] using hcert

def TailChunk001Sub000Block083Part002SupportExplicit : Finset ℕ :=
  ([19911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part002 : ℚ :=
  (12289759025 : ℚ) / 346357289741787072

def SurrogateDiagonalTailChunk001Sub000Block083Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19911
    = surrogateDiagTailX0RatChunk001Sub000Block083Part002

theorem surrogateDiagonalTailChunk001Sub000Block083Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part002] using hcert

def TailChunk001Sub000Block083Part003SupportExplicit : Finset ℕ :=
  ([19913] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19913
    = surrogateDiagTailX0RatChunk001Sub000Block083Part003

theorem surrogateDiagonalTailChunk001Sub000Block083Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part003] using hcert

def TailChunk001Sub000Block083Part004SupportExplicit : Finset ℕ :=
  ([19914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part004 : ℚ :=
  (688245032525 : ℚ) / 2424501028192509504

def SurrogateDiagonalTailChunk001Sub000Block083Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19914
    = surrogateDiagTailX0RatChunk001Sub000Block083Part004

theorem surrogateDiagonalTailChunk001Sub000Block083Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part004] using hcert

def TailChunk001Sub000Block083Part005SupportExplicit : Finset ℕ :=
  ([19915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part005 : ℚ :=
  (1499677014475 : ℚ) / 86350562023742373888

def SurrogateDiagonalTailChunk001Sub000Block083Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19915
    = surrogateDiagTailX0RatChunk001Sub000Block083Part005

theorem surrogateDiagonalTailChunk001Sub000Block083Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part005] using hcert

def TailChunk001Sub000Block083Part006SupportExplicit : Finset ℕ :=
  ([19918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part006 : ℚ :=
  (73261841825 : ℚ) / 10200526155331928064

def SurrogateDiagonalTailChunk001Sub000Block083Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19918
    = surrogateDiagTailX0RatChunk001Sub000Block083Part006

theorem surrogateDiagonalTailChunk001Sub000Block083Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part006] using hcert

def TailChunk001Sub000Block083Part007SupportExplicit : Finset ℕ :=
  ([19919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19919
    = surrogateDiagTailX0RatChunk001Sub000Block083Part007

theorem surrogateDiagonalTailChunk001Sub000Block083Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part007] using hcert

def TailChunk001Sub000Block083Part008SupportExplicit : Finset ℕ :=
  ([19921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part008 : ℚ :=
  (515698037 : ℚ) / 335468055507562500

def SurrogateDiagonalTailChunk001Sub000Block083Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19921
    = surrogateDiagTailX0RatChunk001Sub000Block083Part008

theorem surrogateDiagonalTailChunk001Sub000Block083Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part008] using hcert

def TailChunk001Sub000Block083Part009SupportExplicit : Finset ℕ :=
  ([19922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part009 : ℚ :=
  (7053031825 : ℚ) / 245378488067796672

def SurrogateDiagonalTailChunk001Sub000Block083Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19922
    = surrogateDiagTailX0RatChunk001Sub000Block083Part009

theorem surrogateDiagonalTailChunk001Sub000Block083Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part009] using hcert

def TailChunk001Sub000Block083Part010SupportExplicit : Finset ℕ :=
  ([19923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part010 : ℚ :=
  (2710697219725 : ℚ) / 66453575808267583488

def SurrogateDiagonalTailChunk001Sub000Block083Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19923
    = surrogateDiagTailX0RatChunk001Sub000Block083Part010

theorem surrogateDiagonalTailChunk001Sub000Block083Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part010] using hcert

def TailChunk001Sub000Block083Part011SupportExplicit : Finset ℕ :=
  ([19927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19927
    = surrogateDiagTailX0RatChunk001Sub000Block083Part011

theorem surrogateDiagonalTailChunk001Sub000Block083Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part011] using hcert

def TailChunk001Sub000Block083Part012SupportExplicit : Finset ℕ :=
  ([19929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part012 : ℚ :=
  (2480744020675 : ℚ) / 28893943085439909888

def SurrogateDiagonalTailChunk001Sub000Block083Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19929
    = surrogateDiagTailX0RatChunk001Sub000Block083Part012

theorem surrogateDiagonalTailChunk001Sub000Block083Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part012] using hcert

def TailChunk001Sub000Block083Part013SupportExplicit : Finset ℕ :=
  ([19930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part013 : ℚ :=
  (372482205725 : ℚ) / 5039577924632838144

def SurrogateDiagonalTailChunk001Sub000Block083Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19930
    = surrogateDiagTailX0RatChunk001Sub000Block083Part013

theorem surrogateDiagonalTailChunk001Sub000Block083Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part013] using hcert

def TailChunk001Sub000Block083Part014SupportExplicit : Finset ℕ :=
  ([19931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part014 : ℚ :=
  (14523665825 : ℚ) / 13193218897765281792

def SurrogateDiagonalTailChunk001Sub000Block083Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19931
    = surrogateDiagTailX0RatChunk001Sub000Block083Part014

theorem surrogateDiagonalTailChunk001Sub000Block083Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part014] using hcert

def TailChunk001Sub000Block083Part015SupportExplicit : Finset ℕ :=
  ([19933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part015 : ℚ :=
  (537884659 : ℚ) / 860185264813432200

def SurrogateDiagonalTailChunk001Sub000Block083Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19933
    = surrogateDiagTailX0RatChunk001Sub000Block083Part015

theorem surrogateDiagonalTailChunk001Sub000Block083Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part015] using hcert

def TailChunk001Sub000Block083Part016SupportExplicit : Finset ℕ :=
  ([19934] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19934
    = surrogateDiagTailX0RatChunk001Sub000Block083Part016

theorem surrogateDiagonalTailChunk001Sub000Block083Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part016] using hcert

def TailChunk001Sub000Block083Part017SupportExplicit : Finset ℕ :=
  ([19937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19937
    = surrogateDiagTailX0RatChunk001Sub000Block083Part017

theorem surrogateDiagonalTailChunk001Sub000Block083Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part017] using hcert

def TailChunk001Sub000Block083Part018SupportExplicit : Finset ℕ :=
  ([19938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part018 : ℚ :=
  (345177677225 : ℚ) / 2436213572242511424

def SurrogateDiagonalTailChunk001Sub000Block083Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19938
    = surrogateDiagTailX0RatChunk001Sub000Block083Part018

theorem surrogateDiagonalTailChunk001Sub000Block083Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part018] using hcert

def TailChunk001Sub000Block083Part019SupportExplicit : Finset ℕ :=
  ([19939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part019 : ℚ :=
  (87385903375 : ℚ) / 373256545873620584448

def SurrogateDiagonalTailChunk001Sub000Block083Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19939
    = surrogateDiagTailX0RatChunk001Sub000Block083Part019

theorem surrogateDiagonalTailChunk001Sub000Block083Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part019] using hcert

def TailChunk001Sub000Block083Part020SupportExplicit : Finset ℕ :=
  ([19945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part020 : ℚ :=
  (331753229625 : ℚ) / 53971708742828916736

def SurrogateDiagonalTailChunk001Sub000Block083Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19945
    = surrogateDiagTailX0RatChunk001Sub000Block083Part020

theorem surrogateDiagonalTailChunk001Sub000Block083Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part020] using hcert

def TailChunk001Sub000Block083Part021SupportExplicit : Finset ℕ :=
  ([19946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19946
    = surrogateDiagTailX0RatChunk001Sub000Block083Part021

theorem surrogateDiagonalTailChunk001Sub000Block083Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part021] using hcert

def TailChunk001Sub000Block083Part022SupportExplicit : Finset ℕ :=
  ([19947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part022 : ℚ :=
  (518218067 : ℚ) / 352709266179686400

def SurrogateDiagonalTailChunk001Sub000Block083Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19947
    = surrogateDiagTailX0RatChunk001Sub000Block083Part022

theorem surrogateDiagonalTailChunk001Sub000Block083Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part022] using hcert

def TailChunk001Sub000Block083Part023SupportExplicit : Finset ℕ :=
  ([19949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block083Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19949
    = surrogateDiagTailX0RatChunk001Sub000Block083Part023

theorem surrogateDiagonalTailChunk001Sub000Block083Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part023] using hcert

def TailChunk001Sub000Block083Part024SupportExplicit : Finset ℕ :=
  ([19951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block083Part024 : ℚ :=
  (1096506673 : ℚ) / 3690210534528000000

def SurrogateDiagonalTailChunk001Sub000Block083Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19951
    = surrogateDiagTailX0RatChunk001Sub000Block083Part024

theorem surrogateDiagonalTailChunk001Sub000Block083Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block083Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block083Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block083Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block083Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block083Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block083HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block083Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block083Part000
    + surrogateDiagTailX0RatChunk001Sub000Block083Part001
    + surrogateDiagTailX0RatChunk001Sub000Block083Part002
    + surrogateDiagTailX0RatChunk001Sub000Block083Part003
    + surrogateDiagTailX0RatChunk001Sub000Block083Part004
    + surrogateDiagTailX0RatChunk001Sub000Block083Part005
    + surrogateDiagTailX0RatChunk001Sub000Block083Part006
    + surrogateDiagTailX0RatChunk001Sub000Block083Part007
    + surrogateDiagTailX0RatChunk001Sub000Block083Part008
    + surrogateDiagTailX0RatChunk001Sub000Block083Part009

def surrogateDiagonalTailChunk001Sub000Block083MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block083Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block083Part010
    + surrogateDiagTailX0RatChunk001Sub000Block083Part011
    + surrogateDiagTailX0RatChunk001Sub000Block083Part012
    + surrogateDiagTailX0RatChunk001Sub000Block083Part013
    + surrogateDiagTailX0RatChunk001Sub000Block083Part014
    + surrogateDiagTailX0RatChunk001Sub000Block083Part015
    + surrogateDiagTailX0RatChunk001Sub000Block083Part016
    + surrogateDiagTailX0RatChunk001Sub000Block083Part017
    + surrogateDiagTailX0RatChunk001Sub000Block083Part018
    + surrogateDiagTailX0RatChunk001Sub000Block083Part019

def surrogateDiagonalTailChunk001Sub000Block083TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block083Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block083Part020
    + surrogateDiagTailX0RatChunk001Sub000Block083Part021
    + surrogateDiagTailX0RatChunk001Sub000Block083Part022
    + surrogateDiagTailX0RatChunk001Sub000Block083Part023
    + surrogateDiagTailX0RatChunk001Sub000Block083Part024

def surrogateDiagonalTailChunk001Sub000Block083Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block083HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block083MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block083TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block083 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block083Part000
    + surrogateDiagTailX0RatChunk001Sub000Block083Part001
    + surrogateDiagTailX0RatChunk001Sub000Block083Part002
    + surrogateDiagTailX0RatChunk001Sub000Block083Part003
    + surrogateDiagTailX0RatChunk001Sub000Block083Part004
    + surrogateDiagTailX0RatChunk001Sub000Block083Part005
    + surrogateDiagTailX0RatChunk001Sub000Block083Part006
    + surrogateDiagTailX0RatChunk001Sub000Block083Part007
    + surrogateDiagTailX0RatChunk001Sub000Block083Part008
    + surrogateDiagTailX0RatChunk001Sub000Block083Part009
    + surrogateDiagTailX0RatChunk001Sub000Block083Part010
    + surrogateDiagTailX0RatChunk001Sub000Block083Part011
    + surrogateDiagTailX0RatChunk001Sub000Block083Part012
    + surrogateDiagTailX0RatChunk001Sub000Block083Part013
    + surrogateDiagTailX0RatChunk001Sub000Block083Part014
    + surrogateDiagTailX0RatChunk001Sub000Block083Part015
    + surrogateDiagTailX0RatChunk001Sub000Block083Part016
    + surrogateDiagTailX0RatChunk001Sub000Block083Part017
    + surrogateDiagTailX0RatChunk001Sub000Block083Part018
    + surrogateDiagTailX0RatChunk001Sub000Block083Part019
    + surrogateDiagTailX0RatChunk001Sub000Block083Part020
    + surrogateDiagTailX0RatChunk001Sub000Block083Part021
    + surrogateDiagTailX0RatChunk001Sub000Block083Part022
    + surrogateDiagTailX0RatChunk001Sub000Block083Part023
    + surrogateDiagTailX0RatChunk001Sub000Block083Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block083_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block083Head + surrogateDiagTailX0RatChunk001Sub000Block083Mid + surrogateDiagTailX0RatChunk001Sub000Block083Tail =
      surrogateDiagTailX0RatChunk001Sub000Block083 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block083Head surrogateDiagTailX0RatChunk001Sub000Block083Mid surrogateDiagTailX0RatChunk001Sub000Block083Tail surrogateDiagTailX0RatChunk001Sub000Block083
  ring

def SurrogateDiagonalTailChunk001Sub000Block083HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block083HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block083Head

def SurrogateDiagonalTailChunk001Sub000Block083MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block083MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block083Mid

def SurrogateDiagonalTailChunk001Sub000Block083TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block083TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block083Tail

theorem surrogateDiagonalTailChunk001Sub000Block083_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block083HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block083MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block083TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block083Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block083 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block083HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block083MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block083TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block083Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block083_eq_head_add_mid_add_tail

/-- Block 084 covers tail-support indices [12100,12125) and q from 19954 to 19993. -/

def TailChunk001Sub000Block084Part000SupportExplicit : Finset ℕ :=
  ([19954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part000 : ℚ :=
  (69182189 : ℚ) / 4492709954958528

def SurrogateDiagonalTailChunk001Sub000Block084Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19954
    = surrogateDiagTailX0RatChunk001Sub000Block084Part000

theorem surrogateDiagonalTailChunk001Sub000Block084Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part000] using hcert

def TailChunk001Sub000Block084Part001SupportExplicit : Finset ℕ :=
  ([19955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part001 : ℚ :=
  (151116686525 : ℚ) / 14547471911404240896

def SurrogateDiagonalTailChunk001Sub000Block084Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19955
    = surrogateDiagTailX0RatChunk001Sub000Block084Part001

theorem surrogateDiagonalTailChunk001Sub000Block084Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part001] using hcert

def TailChunk001Sub000Block084Part002SupportExplicit : Finset ℕ :=
  ([19957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part002 : ℚ :=
  (20339685347 : ℚ) / 4276035441081000000

def SurrogateDiagonalTailChunk001Sub000Block084Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19957
    = surrogateDiagTailX0RatChunk001Sub000Block084Part002

theorem surrogateDiagonalTailChunk001Sub000Block084Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part002] using hcert

def TailChunk001Sub000Block084Part003SupportExplicit : Finset ℕ :=
  ([19958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part003 : ℚ :=
  (65949675525 : ℚ) / 6441336666989264896

def SurrogateDiagonalTailChunk001Sub000Block084Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19958
    = surrogateDiagTailX0RatChunk001Sub000Block084Part003

theorem surrogateDiagonalTailChunk001Sub000Block084Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part003] using hcert

def TailChunk001Sub000Block084Part004SupportExplicit : Finset ℕ :=
  ([19959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part004 : ℚ :=
  (125025 : ℚ) / 15663865638422528

def SurrogateDiagonalTailChunk001Sub000Block084Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19959
    = surrogateDiagTailX0RatChunk001Sub000Block084Part004

theorem surrogateDiagonalTailChunk001Sub000Block084Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part004] using hcert

def TailChunk001Sub000Block084Part005SupportExplicit : Finset ℕ :=
  ([19961] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block084Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19961
    = surrogateDiagTailX0RatChunk001Sub000Block084Part005

theorem surrogateDiagonalTailChunk001Sub000Block084Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part005] using hcert

def TailChunk001Sub000Block084Part006SupportExplicit : Finset ℕ :=
  ([19963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block084Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19963
    = surrogateDiagTailX0RatChunk001Sub000Block084Part006

theorem surrogateDiagonalTailChunk001Sub000Block084Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part006] using hcert

def TailChunk001Sub000Block084Part007SupportExplicit : Finset ℕ :=
  ([19966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part007 : ℚ :=
  (33480051425 : ℚ) / 11382023212331295744

def SurrogateDiagonalTailChunk001Sub000Block084Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19966
    = surrogateDiagTailX0RatChunk001Sub000Block084Part007

theorem surrogateDiagonalTailChunk001Sub000Block084Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part007] using hcert

def TailChunk001Sub000Block084Part008SupportExplicit : Finset ℕ :=
  ([19967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part008 : ℚ :=
  (3197245097 : ℚ) / 7142362640138649600

def SurrogateDiagonalTailChunk001Sub000Block084Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19967
    = surrogateDiagTailX0RatChunk001Sub000Block084Part008

theorem surrogateDiagonalTailChunk001Sub000Block084Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part008] using hcert

def TailChunk001Sub000Block084Part009SupportExplicit : Finset ℕ :=
  ([19969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part009 : ℚ :=
  (6997563611 : ℚ) / 6381225194841000000

def SurrogateDiagonalTailChunk001Sub000Block084Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19969
    = surrogateDiagTailX0RatChunk001Sub000Block084Part009

theorem surrogateDiagonalTailChunk001Sub000Block084Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part009] using hcert

def TailChunk001Sub000Block084Part010SupportExplicit : Finset ℕ :=
  ([19970] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part010 : ℚ :=
  (499152925525 : ℚ) / 10160357097570336768

def SurrogateDiagonalTailChunk001Sub000Block084Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19970
    = surrogateDiagTailX0RatChunk001Sub000Block084Part010

theorem surrogateDiagonalTailChunk001Sub000Block084Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part010] using hcert

def TailChunk001Sub000Block084Part011SupportExplicit : Finset ℕ :=
  ([19973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block084Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19973
    = surrogateDiagTailX0RatChunk001Sub000Block084Part011

theorem surrogateDiagonalTailChunk001Sub000Block084Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part011] using hcert

def TailChunk001Sub000Block084Part012SupportExplicit : Finset ℕ :=
  ([19974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part012 : ℚ :=
  (173212276075 : ℚ) / 1226930946532442112

def SurrogateDiagonalTailChunk001Sub000Block084Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19974
    = surrogateDiagTailX0RatChunk001Sub000Block084Part012

theorem surrogateDiagonalTailChunk001Sub000Block084Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part012] using hcert

def TailChunk001Sub000Block084Part013SupportExplicit : Finset ℕ :=
  ([19977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part013 : ℚ :=
  (125025 : ℚ) / 15720456394506368

def SurrogateDiagonalTailChunk001Sub000Block084Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19977
    = surrogateDiagTailX0RatChunk001Sub000Block084Part013

theorem surrogateDiagonalTailChunk001Sub000Block084Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part013] using hcert

def TailChunk001Sub000Block084Part014SupportExplicit : Finset ℕ :=
  ([19978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part014 : ℚ :=
  (21277714675 : ℚ) / 744453296550812736

def SurrogateDiagonalTailChunk001Sub000Block084Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19978
    = surrogateDiagTailX0RatChunk001Sub000Block084Part014

theorem surrogateDiagonalTailChunk001Sub000Block084Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part014] using hcert

def TailChunk001Sub000Block084Part015SupportExplicit : Finset ℕ :=
  ([19979] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block084Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19979
    = surrogateDiagTailX0RatChunk001Sub000Block084Part015

theorem surrogateDiagonalTailChunk001Sub000Block084Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part015] using hcert

def TailChunk001Sub000Block084Part016SupportExplicit : Finset ℕ :=
  ([19981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part016 : ℚ :=
  (16310483125 : ℚ) / 5548148191326633984

def SurrogateDiagonalTailChunk001Sub000Block084Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19981
    = surrogateDiagTailX0RatChunk001Sub000Block084Part016

theorem surrogateDiagonalTailChunk001Sub000Block084Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part016] using hcert

def TailChunk001Sub000Block084Part017SupportExplicit : Finset ℕ :=
  ([19982] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part017 : ℚ :=
  (30585864725 : ℚ) / 11494298794195943424

def SurrogateDiagonalTailChunk001Sub000Block084Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19982
    = surrogateDiagTailX0RatChunk001Sub000Block084Part017

theorem surrogateDiagonalTailChunk001Sub000Block084Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part017] using hcert

def TailChunk001Sub000Block084Part018SupportExplicit : Finset ℕ :=
  ([19983] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part018 : ℚ :=
  (1667 : ℚ) / 209858053478400

def SurrogateDiagonalTailChunk001Sub000Block084Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19983
    = surrogateDiagTailX0RatChunk001Sub000Block084Part018

theorem surrogateDiagonalTailChunk001Sub000Block084Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part018] using hcert

def TailChunk001Sub000Block084Part019SupportExplicit : Finset ℕ :=
  ([19985] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part019 : ℚ :=
  (16076992411 : ℚ) / 1167642744444518400

def SurrogateDiagonalTailChunk001Sub000Block084Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19985
    = surrogateDiagTailX0RatChunk001Sub000Block084Part019

theorem surrogateDiagonalTailChunk001Sub000Block084Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part019] using hcert

def TailChunk001Sub000Block084Part020SupportExplicit : Finset ℕ :=
  ([19986] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part020 : ℚ :=
  (2774725417 : ℚ) / 19678127352102720

def SurrogateDiagonalTailChunk001Sub000Block084Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19986
    = surrogateDiagTailX0RatChunk001Sub000Block084Part020

theorem surrogateDiagonalTailChunk001Sub000Block084Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part020] using hcert

def TailChunk001Sub000Block084Part021SupportExplicit : Finset ℕ :=
  ([19987] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part021 : ℚ :=
  (55469719 : ℚ) / 17520673046722560

def SurrogateDiagonalTailChunk001Sub000Block084Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19987
    = surrogateDiagTailX0RatChunk001Sub000Block084Part021

theorem surrogateDiagonalTailChunk001Sub000Block084Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part021] using hcert

def TailChunk001Sub000Block084Part022SupportExplicit : Finset ℕ :=
  ([19990] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part022 : ℚ :=
  (166717075075 : ℚ) / 3400380406443350016

def SurrogateDiagonalTailChunk001Sub000Block084Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19990
    = surrogateDiagTailX0RatChunk001Sub000Block084Part022

theorem surrogateDiagonalTailChunk001Sub000Block084Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part022] using hcert

def TailChunk001Sub000Block084Part023SupportExplicit : Finset ℕ :=
  ([19991] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block084Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19991
    = surrogateDiagTailX0RatChunk001Sub000Block084Part023

theorem surrogateDiagonalTailChunk001Sub000Block084Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part023] using hcert

def TailChunk001Sub000Block084Part024SupportExplicit : Finset ℕ :=
  ([19993] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block084Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block084Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19993
    = surrogateDiagTailX0RatChunk001Sub000Block084Part024

theorem surrogateDiagonalTailChunk001Sub000Block084Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block084Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block084Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block084Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block084Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block084Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block084HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block084Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block084Part000
    + surrogateDiagTailX0RatChunk001Sub000Block084Part001
    + surrogateDiagTailX0RatChunk001Sub000Block084Part002
    + surrogateDiagTailX0RatChunk001Sub000Block084Part003
    + surrogateDiagTailX0RatChunk001Sub000Block084Part004
    + surrogateDiagTailX0RatChunk001Sub000Block084Part005
    + surrogateDiagTailX0RatChunk001Sub000Block084Part006
    + surrogateDiagTailX0RatChunk001Sub000Block084Part007
    + surrogateDiagTailX0RatChunk001Sub000Block084Part008
    + surrogateDiagTailX0RatChunk001Sub000Block084Part009

def surrogateDiagonalTailChunk001Sub000Block084MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block084Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block084Part010
    + surrogateDiagTailX0RatChunk001Sub000Block084Part011
    + surrogateDiagTailX0RatChunk001Sub000Block084Part012
    + surrogateDiagTailX0RatChunk001Sub000Block084Part013
    + surrogateDiagTailX0RatChunk001Sub000Block084Part014
    + surrogateDiagTailX0RatChunk001Sub000Block084Part015
    + surrogateDiagTailX0RatChunk001Sub000Block084Part016
    + surrogateDiagTailX0RatChunk001Sub000Block084Part017
    + surrogateDiagTailX0RatChunk001Sub000Block084Part018
    + surrogateDiagTailX0RatChunk001Sub000Block084Part019

def surrogateDiagonalTailChunk001Sub000Block084TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block084Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block084Part020
    + surrogateDiagTailX0RatChunk001Sub000Block084Part021
    + surrogateDiagTailX0RatChunk001Sub000Block084Part022
    + surrogateDiagTailX0RatChunk001Sub000Block084Part023
    + surrogateDiagTailX0RatChunk001Sub000Block084Part024

def surrogateDiagonalTailChunk001Sub000Block084Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block084HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block084MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block084TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block084 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block084Part000
    + surrogateDiagTailX0RatChunk001Sub000Block084Part001
    + surrogateDiagTailX0RatChunk001Sub000Block084Part002
    + surrogateDiagTailX0RatChunk001Sub000Block084Part003
    + surrogateDiagTailX0RatChunk001Sub000Block084Part004
    + surrogateDiagTailX0RatChunk001Sub000Block084Part005
    + surrogateDiagTailX0RatChunk001Sub000Block084Part006
    + surrogateDiagTailX0RatChunk001Sub000Block084Part007
    + surrogateDiagTailX0RatChunk001Sub000Block084Part008
    + surrogateDiagTailX0RatChunk001Sub000Block084Part009
    + surrogateDiagTailX0RatChunk001Sub000Block084Part010
    + surrogateDiagTailX0RatChunk001Sub000Block084Part011
    + surrogateDiagTailX0RatChunk001Sub000Block084Part012
    + surrogateDiagTailX0RatChunk001Sub000Block084Part013
    + surrogateDiagTailX0RatChunk001Sub000Block084Part014
    + surrogateDiagTailX0RatChunk001Sub000Block084Part015
    + surrogateDiagTailX0RatChunk001Sub000Block084Part016
    + surrogateDiagTailX0RatChunk001Sub000Block084Part017
    + surrogateDiagTailX0RatChunk001Sub000Block084Part018
    + surrogateDiagTailX0RatChunk001Sub000Block084Part019
    + surrogateDiagTailX0RatChunk001Sub000Block084Part020
    + surrogateDiagTailX0RatChunk001Sub000Block084Part021
    + surrogateDiagTailX0RatChunk001Sub000Block084Part022
    + surrogateDiagTailX0RatChunk001Sub000Block084Part023
    + surrogateDiagTailX0RatChunk001Sub000Block084Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block084_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block084Head + surrogateDiagTailX0RatChunk001Sub000Block084Mid + surrogateDiagTailX0RatChunk001Sub000Block084Tail =
      surrogateDiagTailX0RatChunk001Sub000Block084 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block084Head surrogateDiagTailX0RatChunk001Sub000Block084Mid surrogateDiagTailX0RatChunk001Sub000Block084Tail surrogateDiagTailX0RatChunk001Sub000Block084
  ring

def SurrogateDiagonalTailChunk001Sub000Block084HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block084HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block084Head

def SurrogateDiagonalTailChunk001Sub000Block084MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block084MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block084Mid

def SurrogateDiagonalTailChunk001Sub000Block084TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block084TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block084Tail

theorem surrogateDiagonalTailChunk001Sub000Block084_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block084HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block084MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block084TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block084Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block084 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block084HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block084MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block084TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block084Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block084_eq_head_add_mid_add_tail

/-- Block 085 covers tail-support indices [12125,12150) and q from 19994 to 20030. -/

def TailChunk001Sub000Block085Part000SupportExplicit : Finset ℕ :=
  ([19994] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part000 : ℚ :=
  (224715538375 : ℚ) / 18038346422490759168

def SurrogateDiagonalTailChunk001Sub000Block085Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19994
    = surrogateDiagTailX0RatChunk001Sub000Block085Part000

theorem surrogateDiagonalTailChunk001Sub000Block085Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part000] using hcert

def TailChunk001Sub000Block085Part001SupportExplicit : Finset ℕ :=
  ([19995] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part001 : ℚ :=
  (15385691933 : ℚ) / 516296264653209600

def SurrogateDiagonalTailChunk001Sub000Block085Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19995
    = surrogateDiagTailX0RatChunk001Sub000Block085Part001

theorem surrogateDiagonalTailChunk001Sub000Block085Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part001] using hcert

def TailChunk001Sub000Block085Part002SupportExplicit : Finset ℕ :=
  ([19997] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub000Block085Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19997
    = surrogateDiagTailX0RatChunk001Sub000Block085Part002

theorem surrogateDiagonalTailChunk001Sub000Block085Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part002] using hcert

def TailChunk001Sub000Block085Part003SupportExplicit : Finset ℕ :=
  ([19999] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part003 : ℚ :=
  (511670892625 : ℚ) / 215607901600503595008

def SurrogateDiagonalTailChunk001Sub000Block085Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 19999
    = surrogateDiagTailX0RatChunk001Sub000Block085Part003

theorem surrogateDiagonalTailChunk001Sub000Block085Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part003] using hcert

def TailChunk001Sub000Block085Part004SupportExplicit : Finset ℕ :=
  ([20001] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part004 : ℚ :=
  (190228683725 : ℚ) / 1272163349176516608

def SurrogateDiagonalTailChunk001Sub000Block085Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20001
    = surrogateDiagTailX0RatChunk001Sub000Block085Part004

theorem surrogateDiagonalTailChunk001Sub000Block085Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part004] using hcert

def TailChunk001Sub000Block085Part005SupportExplicit : Finset ℕ :=
  ([20002] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part005 : ℚ :=
  (1514309173075 : ℚ) / 5747149397097971712

def SurrogateDiagonalTailChunk001Sub000Block085Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20002
    = surrogateDiagTailX0RatChunk001Sub000Block085Part005

theorem surrogateDiagonalTailChunk001Sub000Block085Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part005] using hcert

def TailChunk001Sub000Block085Part006SupportExplicit : Finset ℕ :=
  ([20003] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part006 : ℚ :=
  (486111287417 : ℚ) / 7501657483778457600

def SurrogateDiagonalTailChunk001Sub000Block085Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20003
    = surrogateDiagTailX0RatChunk001Sub000Block085Part006

theorem surrogateDiagonalTailChunk001Sub000Block085Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part006] using hcert

def TailChunk001Sub000Block085Part007SupportExplicit : Finset ℕ :=
  ([20005] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part007 : ℚ :=
  (680114019499 : ℚ) / 6554910720000000000

def SurrogateDiagonalTailChunk001Sub000Block085Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20005
    = surrogateDiagTailX0RatChunk001Sub000Block085Part007

theorem surrogateDiagonalTailChunk001Sub000Block085Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part007] using hcert

def TailChunk001Sub000Block085Part008SupportExplicit : Finset ℕ :=
  ([20006] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part008 : ℚ :=
  (276285968075 : ℚ) / 748638547223970816

def SurrogateDiagonalTailChunk001Sub000Block085Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20006
    = surrogateDiagTailX0RatChunk001Sub000Block085Part008

theorem surrogateDiagonalTailChunk001Sub000Block085Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part008] using hcert

def TailChunk001Sub000Block085Part009SupportExplicit : Finset ℕ :=
  ([20009] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part009 : ℚ :=
  (29914091563 : ℚ) / 331016950354280448

def SurrogateDiagonalTailChunk001Sub000Block085Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20009
    = surrogateDiagTailX0RatChunk001Sub000Block085Part009

theorem surrogateDiagonalTailChunk001Sub000Block085Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part009] using hcert

def TailChunk001Sub000Block085Part010SupportExplicit : Finset ℕ :=
  ([20010] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part010 : ℚ :=
  (2295415621525 : ℚ) / 1474720289865596928

def SurrogateDiagonalTailChunk001Sub000Block085Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20010
    = surrogateDiagTailX0RatChunk001Sub000Block085Part010

theorem surrogateDiagonalTailChunk001Sub000Block085Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part010] using hcert

def TailChunk001Sub000Block085Part011SupportExplicit : Finset ℕ :=
  ([20011] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part011 : ℚ :=
  (10011003025 : ℚ) / 160352304128026002

def SurrogateDiagonalTailChunk001Sub000Block085Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20011
    = surrogateDiagTailX0RatChunk001Sub000Block085Part011

theorem surrogateDiagonalTailChunk001Sub000Block085Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part011] using hcert

def TailChunk001Sub000Block085Part012SupportExplicit : Finset ℕ :=
  ([20013] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part012 : ℚ :=
  (8556776242675 : ℚ) / 42589215130963673088

def SurrogateDiagonalTailChunk001Sub000Block085Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20013
    = surrogateDiagTailX0RatChunk001Sub000Block085Part012

theorem surrogateDiagonalTailChunk001Sub000Block085Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part012] using hcert

def TailChunk001Sub000Block085Part013SupportExplicit : Finset ℕ :=
  ([20014] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part013 : ℚ :=
  (1564688265625 : ℚ) / 6266266508101890162

def SurrogateDiagonalTailChunk001Sub000Block085Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20014
    = surrogateDiagTailX0RatChunk001Sub000Block085Part013

theorem surrogateDiagonalTailChunk001Sub000Block085Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part013] using hcert

def TailChunk001Sub000Block085Part014SupportExplicit : Finset ℕ :=
  ([20015] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part014 : ℚ :=
  (17019856338025 : ℚ) / 164200759427098626048

def SurrogateDiagonalTailChunk001Sub000Block085Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20015
    = surrogateDiagTailX0RatChunk001Sub000Block085Part014

theorem surrogateDiagonalTailChunk001Sub000Block085Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part014] using hcert

def TailChunk001Sub000Block085Part015SupportExplicit : Finset ℕ :=
  ([20017] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part015 : ℚ :=
  (951137695603 : ℚ) / 14284725280277299200

def SurrogateDiagonalTailChunk001Sub000Block085Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20017
    = surrogateDiagTailX0RatChunk001Sub000Block085Part015

theorem surrogateDiagonalTailChunk001Sub000Block085Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part015] using hcert

def TailChunk001Sub000Block085Part016SupportExplicit : Finset ℕ :=
  ([20018] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part016 : ℚ :=
  (1565313765625 : ℚ) / 6271278017605120512

def SurrogateDiagonalTailChunk001Sub000Block085Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20018
    = surrogateDiagTailX0RatChunk001Sub000Block085Part016

theorem surrogateDiagonalTailChunk001Sub000Block085Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part016] using hcert

def TailChunk001Sub000Block085Part017SupportExplicit : Finset ℕ :=
  ([20019] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part017 : ℚ :=
  (11129520332725 : ℚ) / 79281341852193128448

def SurrogateDiagonalTailChunk001Sub000Block085Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20019
    = surrogateDiagTailX0RatChunk001Sub000Block085Part017

theorem surrogateDiagonalTailChunk001Sub000Block085Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part017] using hcert

def TailChunk001Sub000Block085Part018SupportExplicit : Finset ℕ :=
  ([20021] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part018 : ℚ :=
  (10021011025 : ℚ) / 160673088832288032

def SurrogateDiagonalTailChunk001Sub000Block085Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20021
    = surrogateDiagTailX0RatChunk001Sub000Block085Part018

theorem surrogateDiagonalTailChunk001Sub000Block085Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part018] using hcert

def TailChunk001Sub000Block085Part019SupportExplicit : Finset ℕ :=
  ([20022] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part019 : ℚ :=
  (168853171 : ℚ) / 219439223068800

def SurrogateDiagonalTailChunk001Sub000Block085Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20022
    = surrogateDiagTailX0RatChunk001Sub000Block085Part019

theorem surrogateDiagonalTailChunk001Sub000Block085Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part019] using hcert

def TailChunk001Sub000Block085Part020SupportExplicit : Finset ℕ :=
  ([20023] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part020 : ℚ :=
  (6264383265625 : ℚ) / 100460814677852919282

def SurrogateDiagonalTailChunk001Sub000Block085Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20023
    = surrogateDiagTailX0RatChunk001Sub000Block085Part020

theorem surrogateDiagonalTailChunk001Sub000Block085Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part020] using hcert

def TailChunk001Sub000Block085Part021SupportExplicit : Finset ℕ :=
  ([20026] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part021 : ℚ :=
  (100739956349 : ℚ) / 278683864635801600

def SurrogateDiagonalTailChunk001Sub000Block085Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20026
    = surrogateDiagTailX0RatChunk001Sub000Block085Part021

theorem surrogateDiagonalTailChunk001Sub000Block085Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part021] using hcert

def TailChunk001Sub000Block085Part022SupportExplicit : Finset ℕ :=
  ([20027] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part022 : ℚ :=
  (151347372629 : ℚ) / 1734546631625533440

def SurrogateDiagonalTailChunk001Sub000Block085Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20027
    = surrogateDiagTailX0RatChunk001Sub000Block085Part022

theorem surrogateDiagonalTailChunk001Sub000Block085Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part022] using hcert

def TailChunk001Sub000Block085Part023SupportExplicit : Finset ℕ :=
  ([20029] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part023 : ℚ :=
  (6268138140625 : ℚ) / 100581289333403756832

def SurrogateDiagonalTailChunk001Sub000Block085Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20029
    = surrogateDiagTailX0RatChunk001Sub000Block085Part023

theorem surrogateDiagonalTailChunk001Sub000Block085Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part023] using hcert

def TailChunk001Sub000Block085Part024SupportExplicit : Finset ℕ :=
  ([20030] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block085Part024 : ℚ :=
  (214807439325 : ℚ) / 489670365965068288

def SurrogateDiagonalTailChunk001Sub000Block085Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20030
    = surrogateDiagTailX0RatChunk001Sub000Block085Part024

theorem surrogateDiagonalTailChunk001Sub000Block085Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block085Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block085Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block085Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block085Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block085Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block085HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block085Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block085Part000
    + surrogateDiagTailX0RatChunk001Sub000Block085Part001
    + surrogateDiagTailX0RatChunk001Sub000Block085Part002
    + surrogateDiagTailX0RatChunk001Sub000Block085Part003
    + surrogateDiagTailX0RatChunk001Sub000Block085Part004
    + surrogateDiagTailX0RatChunk001Sub000Block085Part005
    + surrogateDiagTailX0RatChunk001Sub000Block085Part006
    + surrogateDiagTailX0RatChunk001Sub000Block085Part007
    + surrogateDiagTailX0RatChunk001Sub000Block085Part008
    + surrogateDiagTailX0RatChunk001Sub000Block085Part009

def surrogateDiagonalTailChunk001Sub000Block085MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block085Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block085Part010
    + surrogateDiagTailX0RatChunk001Sub000Block085Part011
    + surrogateDiagTailX0RatChunk001Sub000Block085Part012
    + surrogateDiagTailX0RatChunk001Sub000Block085Part013
    + surrogateDiagTailX0RatChunk001Sub000Block085Part014
    + surrogateDiagTailX0RatChunk001Sub000Block085Part015
    + surrogateDiagTailX0RatChunk001Sub000Block085Part016
    + surrogateDiagTailX0RatChunk001Sub000Block085Part017
    + surrogateDiagTailX0RatChunk001Sub000Block085Part018
    + surrogateDiagTailX0RatChunk001Sub000Block085Part019

def surrogateDiagonalTailChunk001Sub000Block085TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block085Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block085Part020
    + surrogateDiagTailX0RatChunk001Sub000Block085Part021
    + surrogateDiagTailX0RatChunk001Sub000Block085Part022
    + surrogateDiagTailX0RatChunk001Sub000Block085Part023
    + surrogateDiagTailX0RatChunk001Sub000Block085Part024

def surrogateDiagonalTailChunk001Sub000Block085Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block085HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block085MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block085TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block085 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block085Part000
    + surrogateDiagTailX0RatChunk001Sub000Block085Part001
    + surrogateDiagTailX0RatChunk001Sub000Block085Part002
    + surrogateDiagTailX0RatChunk001Sub000Block085Part003
    + surrogateDiagTailX0RatChunk001Sub000Block085Part004
    + surrogateDiagTailX0RatChunk001Sub000Block085Part005
    + surrogateDiagTailX0RatChunk001Sub000Block085Part006
    + surrogateDiagTailX0RatChunk001Sub000Block085Part007
    + surrogateDiagTailX0RatChunk001Sub000Block085Part008
    + surrogateDiagTailX0RatChunk001Sub000Block085Part009
    + surrogateDiagTailX0RatChunk001Sub000Block085Part010
    + surrogateDiagTailX0RatChunk001Sub000Block085Part011
    + surrogateDiagTailX0RatChunk001Sub000Block085Part012
    + surrogateDiagTailX0RatChunk001Sub000Block085Part013
    + surrogateDiagTailX0RatChunk001Sub000Block085Part014
    + surrogateDiagTailX0RatChunk001Sub000Block085Part015
    + surrogateDiagTailX0RatChunk001Sub000Block085Part016
    + surrogateDiagTailX0RatChunk001Sub000Block085Part017
    + surrogateDiagTailX0RatChunk001Sub000Block085Part018
    + surrogateDiagTailX0RatChunk001Sub000Block085Part019
    + surrogateDiagTailX0RatChunk001Sub000Block085Part020
    + surrogateDiagTailX0RatChunk001Sub000Block085Part021
    + surrogateDiagTailX0RatChunk001Sub000Block085Part022
    + surrogateDiagTailX0RatChunk001Sub000Block085Part023
    + surrogateDiagTailX0RatChunk001Sub000Block085Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block085_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block085Head + surrogateDiagTailX0RatChunk001Sub000Block085Mid + surrogateDiagTailX0RatChunk001Sub000Block085Tail =
      surrogateDiagTailX0RatChunk001Sub000Block085 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block085Head surrogateDiagTailX0RatChunk001Sub000Block085Mid surrogateDiagTailX0RatChunk001Sub000Block085Tail surrogateDiagTailX0RatChunk001Sub000Block085
  ring

def SurrogateDiagonalTailChunk001Sub000Block085HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block085HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block085Head

def SurrogateDiagonalTailChunk001Sub000Block085MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block085MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block085Mid

def SurrogateDiagonalTailChunk001Sub000Block085TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block085TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block085Tail

theorem surrogateDiagonalTailChunk001Sub000Block085_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block085HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block085MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block085TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block085Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block085 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block085HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block085MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block085TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block085Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block085_eq_head_add_mid_add_tail

/-- Block 086 covers tail-support indices [12150,12175) and q from 20031 to 20071. -/

def TailChunk001Sub000Block086Part000SupportExplicit : Finset ℕ :=
  ([20031] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part000 : ℚ :=
  (15176615851 : ℚ) / 86329121377241088

def SurrogateDiagonalTailChunk001Sub000Block086Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20031
    = surrogateDiagTailX0RatChunk001Sub000Block086Part000

theorem surrogateDiagonalTailChunk001Sub000Block086Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part000] using hcert

def TailChunk001Sub000Block086Part001SupportExplicit : Finset ℕ :=
  ([20033] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part001 : ℚ :=
  (19489099682875 : ℚ) / 230472073210207961088

def SurrogateDiagonalTailChunk001Sub000Block086Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20033
    = surrogateDiagTailX0RatChunk001Sub000Block086Part001

theorem surrogateDiagonalTailChunk001Sub000Block086Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part001] using hcert

def TailChunk001Sub000Block086Part002SupportExplicit : Finset ℕ :=
  ([20035] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part002 : ℚ :=
  (17053893541525 : ℚ) / 164858219103479973888

def SurrogateDiagonalTailChunk001Sub000Block086Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20035
    = surrogateDiagTailX0RatChunk001Sub000Block086Part002

theorem surrogateDiagonalTailChunk001Sub000Block086Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part002] using hcert

def TailChunk001Sub000Block086Part003SupportExplicit : Finset ℕ :=
  ([20037] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part003 : ℚ :=
  (11149545332125 : ℚ) / 79566911457365662848

def SurrogateDiagonalTailChunk001Sub000Block086Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20037
    = surrogateDiagTailX0RatChunk001Sub000Block086Part003

theorem surrogateDiagonalTailChunk001Sub000Block086Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part003] using hcert

def TailChunk001Sub000Block086Part004SupportExplicit : Finset ℕ :=
  ([20038] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part004 : ℚ :=
  (222916329425 : ℚ) / 834857197897089024

def SurrogateDiagonalTailChunk001Sub000Block086Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20038
    = surrogateDiagTailX0RatChunk001Sub000Block086Part004

theorem surrogateDiagonalTailChunk001Sub000Block086Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part004] using hcert

def TailChunk001Sub000Block086Part005SupportExplicit : Finset ℕ :=
  ([20039] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part005 : ℚ :=
  (940717098331 : ℚ) / 13935268421761075200

def SurrogateDiagonalTailChunk001Sub000Block086Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20039
    = surrogateDiagTailX0RatChunk001Sub000Block086Part005

theorem surrogateDiagonalTailChunk001Sub000Block086Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part005] using hcert

def TailChunk001Sub000Block086Part006SupportExplicit : Finset ℕ :=
  ([20042] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part006 : ℚ :=
  (1812785391 : ℚ) / 5715722999350000

def SurrogateDiagonalTailChunk001Sub000Block086Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20042
    = surrogateDiagTailX0RatChunk001Sub000Block086Part006

theorem surrogateDiagonalTailChunk001Sub000Block086Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part006] using hcert

def TailChunk001Sub000Block086Part007SupportExplicit : Finset ℕ :=
  ([20045] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part007 : ℚ :=
  (581555975671 : ℚ) / 5227499679613747200

def SurrogateDiagonalTailChunk001Sub000Block086Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20045
    = surrogateDiagTailX0RatChunk001Sub000Block086Part007

theorem surrogateDiagonalTailChunk001Sub000Block086Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part007] using hcert

def TailChunk001Sub000Block086Part008SupportExplicit : Finset ℕ :=
  ([20046] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part008 : ℚ :=
  (193006099975 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk001Sub000Block086Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20046
    = surrogateDiagTailX0RatChunk001Sub000Block086Part008

theorem surrogateDiagonalTailChunk001Sub000Block086Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part008] using hcert

def TailChunk001Sub000Block086Part009SupportExplicit : Finset ℕ :=
  ([20047] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part009 : ℚ :=
  (6279409515625 : ℚ) / 100943363505372329682

def SurrogateDiagonalTailChunk001Sub000Block086Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20047
    = surrogateDiagTailX0RatChunk001Sub000Block086Part009

theorem surrogateDiagonalTailChunk001Sub000Block086Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part009] using hcert

def TailChunk001Sub000Block086Part010SupportExplicit : Finset ℕ :=
  ([20049] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part010 : ℚ :=
  (28307488123 : ℚ) / 188111608629166080

def SurrogateDiagonalTailChunk001Sub000Block086Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20049
    = surrogateDiagTailX0RatChunk001Sub000Block086Part010

theorem surrogateDiagonalTailChunk001Sub000Block086Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part010] using hcert

def TailChunk001Sub000Block086Part011SupportExplicit : Finset ℕ :=
  ([20051] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part011 : ℚ :=
  (402042601 : ℚ) / 6465533248330050

def SurrogateDiagonalTailChunk001Sub000Block086Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20051
    = surrogateDiagTailX0RatChunk001Sub000Block086Part011

theorem surrogateDiagonalTailChunk001Sub000Block086Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part011] using hcert

def TailChunk001Sub000Block086Part012SupportExplicit : Finset ℕ :=
  ([20053] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part012 : ℚ :=
  (17639735847 : ℚ) / 229635540004749400

def SurrogateDiagonalTailChunk001Sub000Block086Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20053
    = surrogateDiagTailX0RatChunk001Sub000Block086Part012

theorem surrogateDiagonalTailChunk001Sub000Block086Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part012] using hcert

def TailChunk001Sub000Block086Part013SupportExplicit : Finset ℕ :=
  ([20054] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part013 : ℚ :=
  (119887596797 : ℚ) / 446397665008665600

def SurrogateDiagonalTailChunk001Sub000Block086Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20054
    = surrogateDiagTailX0RatChunk001Sub000Block086Part013

theorem surrogateDiagonalTailChunk001Sub000Block086Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part013] using hcert

def TailChunk001Sub000Block086Part014SupportExplicit : Finset ℕ :=
  ([20055] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part014 : ℚ :=
  (46371157799 : ℚ) / 138387288230461440

def SurrogateDiagonalTailChunk001Sub000Block086Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20055
    = surrogateDiagTailX0RatChunk001Sub000Block086Part014

theorem surrogateDiagonalTailChunk001Sub000Block086Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part014] using hcert

def TailChunk001Sub000Block086Part015SupportExplicit : Finset ℕ :=
  ([20057] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part015 : ℚ :=
  (473357284391 : ℚ) / 7054592712583233600

def SurrogateDiagonalTailChunk001Sub000Block086Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20057
    = surrogateDiagTailX0RatChunk001Sub000Block086Part015

theorem surrogateDiagonalTailChunk001Sub000Block086Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part015] using hcert

def TailChunk001Sub000Block086Part016SupportExplicit : Finset ℕ :=
  ([20058] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part016 : ℚ :=
  (872871138025 : ℚ) / 1247707059846626592

def SurrogateDiagonalTailChunk001Sub000Block086Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20058
    = surrogateDiagTailX0RatChunk001Sub000Block086Part016

theorem surrogateDiagonalTailChunk001Sub000Block086Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part016] using hcert

def TailChunk001Sub000Block086Part017SupportExplicit : Finset ℕ :=
  ([20059] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part017 : ℚ :=
  (2411356280525 : ℚ) / 32572180178057889792

def SurrogateDiagonalTailChunk001Sub000Block086Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20059
    = surrogateDiagTailX0RatChunk001Sub000Block086Part017

theorem surrogateDiagonalTailChunk001Sub000Block086Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part017] using hcert

def TailChunk001Sub000Block086Part018SupportExplicit : Finset ℕ :=
  ([20062] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part018 : ℚ :=
  (277835372975 : ℚ) / 757061964204097536

def SurrogateDiagonalTailChunk001Sub000Block086Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20062
    = surrogateDiagTailX0RatChunk001Sub000Block086Part018

theorem surrogateDiagonalTailChunk001Sub000Block086Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part018] using hcert

def TailChunk001Sub000Block086Part019SupportExplicit : Finset ℕ :=
  ([20063] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part019 : ℚ :=
  (6289437015625 : ℚ) / 101266027081220337042

def SurrogateDiagonalTailChunk001Sub000Block086Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20063
    = surrogateDiagTailX0RatChunk001Sub000Block086Part019

theorem surrogateDiagonalTailChunk001Sub000Block086Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part019] using hcert

def TailChunk001Sub000Block086Part020SupportExplicit : Finset ℕ :=
  ([20065] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part020 : ℚ :=
  (1006087140625 : ℚ) / 10365506753562789888

def SurrogateDiagonalTailChunk001Sub000Block086Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20065
    = surrogateDiagTailX0RatChunk001Sub000Block086Part020

theorem surrogateDiagonalTailChunk001Sub000Block086Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part020] using hcert

def TailChunk001Sub000Block086Part021SupportExplicit : Finset ℕ :=
  ([20066] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part021 : ℚ :=
  (3049665151025 : ℚ) / 11664267058550643264

def SurrogateDiagonalTailChunk001Sub000Block086Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20066
    = surrogateDiagTailX0RatChunk001Sub000Block086Part021

theorem surrogateDiagonalTailChunk001Sub000Block086Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part021] using hcert

def TailChunk001Sub000Block086Part022SupportExplicit : Finset ℕ :=
  ([20067] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part022 : ℚ :=
  (1016632757375 : ℚ) / 7276779481866436608

def SurrogateDiagonalTailChunk001Sub000Block086Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20067
    = surrogateDiagTailX0RatChunk001Sub000Block086Part022

theorem surrogateDiagonalTailChunk001Sub000Block086Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part022] using hcert

def TailChunk001Sub000Block086Part023SupportExplicit : Finset ℕ :=
  ([20069] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part023 : ℚ :=
  (28482730879 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk001Sub000Block086Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20069
    = surrogateDiagTailX0RatChunk001Sub000Block086Part023

theorem surrogateDiagonalTailChunk001Sub000Block086Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part023] using hcert

def TailChunk001Sub000Block086Part024SupportExplicit : Finset ℕ :=
  ([20071] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block086Part024 : ℚ :=
  (10071126025 : ℚ) / 162284237821502802

def SurrogateDiagonalTailChunk001Sub000Block086Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20071
    = surrogateDiagTailX0RatChunk001Sub000Block086Part024

theorem surrogateDiagonalTailChunk001Sub000Block086Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block086Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block086Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block086Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block086Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block086Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block086HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block086Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block086Part000
    + surrogateDiagTailX0RatChunk001Sub000Block086Part001
    + surrogateDiagTailX0RatChunk001Sub000Block086Part002
    + surrogateDiagTailX0RatChunk001Sub000Block086Part003
    + surrogateDiagTailX0RatChunk001Sub000Block086Part004
    + surrogateDiagTailX0RatChunk001Sub000Block086Part005
    + surrogateDiagTailX0RatChunk001Sub000Block086Part006
    + surrogateDiagTailX0RatChunk001Sub000Block086Part007
    + surrogateDiagTailX0RatChunk001Sub000Block086Part008
    + surrogateDiagTailX0RatChunk001Sub000Block086Part009

def surrogateDiagonalTailChunk001Sub000Block086MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block086Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block086Part010
    + surrogateDiagTailX0RatChunk001Sub000Block086Part011
    + surrogateDiagTailX0RatChunk001Sub000Block086Part012
    + surrogateDiagTailX0RatChunk001Sub000Block086Part013
    + surrogateDiagTailX0RatChunk001Sub000Block086Part014
    + surrogateDiagTailX0RatChunk001Sub000Block086Part015
    + surrogateDiagTailX0RatChunk001Sub000Block086Part016
    + surrogateDiagTailX0RatChunk001Sub000Block086Part017
    + surrogateDiagTailX0RatChunk001Sub000Block086Part018
    + surrogateDiagTailX0RatChunk001Sub000Block086Part019

def surrogateDiagonalTailChunk001Sub000Block086TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block086Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block086Part020
    + surrogateDiagTailX0RatChunk001Sub000Block086Part021
    + surrogateDiagTailX0RatChunk001Sub000Block086Part022
    + surrogateDiagTailX0RatChunk001Sub000Block086Part023
    + surrogateDiagTailX0RatChunk001Sub000Block086Part024

def surrogateDiagonalTailChunk001Sub000Block086Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block086HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block086MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block086TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block086 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block086Part000
    + surrogateDiagTailX0RatChunk001Sub000Block086Part001
    + surrogateDiagTailX0RatChunk001Sub000Block086Part002
    + surrogateDiagTailX0RatChunk001Sub000Block086Part003
    + surrogateDiagTailX0RatChunk001Sub000Block086Part004
    + surrogateDiagTailX0RatChunk001Sub000Block086Part005
    + surrogateDiagTailX0RatChunk001Sub000Block086Part006
    + surrogateDiagTailX0RatChunk001Sub000Block086Part007
    + surrogateDiagTailX0RatChunk001Sub000Block086Part008
    + surrogateDiagTailX0RatChunk001Sub000Block086Part009
    + surrogateDiagTailX0RatChunk001Sub000Block086Part010
    + surrogateDiagTailX0RatChunk001Sub000Block086Part011
    + surrogateDiagTailX0RatChunk001Sub000Block086Part012
    + surrogateDiagTailX0RatChunk001Sub000Block086Part013
    + surrogateDiagTailX0RatChunk001Sub000Block086Part014
    + surrogateDiagTailX0RatChunk001Sub000Block086Part015
    + surrogateDiagTailX0RatChunk001Sub000Block086Part016
    + surrogateDiagTailX0RatChunk001Sub000Block086Part017
    + surrogateDiagTailX0RatChunk001Sub000Block086Part018
    + surrogateDiagTailX0RatChunk001Sub000Block086Part019
    + surrogateDiagTailX0RatChunk001Sub000Block086Part020
    + surrogateDiagTailX0RatChunk001Sub000Block086Part021
    + surrogateDiagTailX0RatChunk001Sub000Block086Part022
    + surrogateDiagTailX0RatChunk001Sub000Block086Part023
    + surrogateDiagTailX0RatChunk001Sub000Block086Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block086_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block086Head + surrogateDiagTailX0RatChunk001Sub000Block086Mid + surrogateDiagTailX0RatChunk001Sub000Block086Tail =
      surrogateDiagTailX0RatChunk001Sub000Block086 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block086Head surrogateDiagTailX0RatChunk001Sub000Block086Mid surrogateDiagTailX0RatChunk001Sub000Block086Tail surrogateDiagTailX0RatChunk001Sub000Block086
  ring

def SurrogateDiagonalTailChunk001Sub000Block086HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block086HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block086Head

def SurrogateDiagonalTailChunk001Sub000Block086MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block086MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block086Mid

def SurrogateDiagonalTailChunk001Sub000Block086TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block086TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block086Tail

theorem surrogateDiagonalTailChunk001Sub000Block086_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block086HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block086MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block086TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block086Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block086 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block086HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block086MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block086TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block086Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block086_eq_head_add_mid_add_tail

/-- Block 087 covers tail-support indices [12175,12200) and q from 20073 to 20117. -/

def TailChunk001Sub000Block087Part000SupportExplicit : Finset ℕ :=
  ([20073] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part000 : ℚ :=
  (447585973237 : ℚ) / 3205614574251907200

def SurrogateDiagonalTailChunk001Sub000Block087Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20073
    = surrogateDiagTailX0RatChunk001Sub000Block087Part000

theorem surrogateDiagonalTailChunk001Sub000Block087Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part000] using hcert

def TailChunk001Sub000Block087Part001SupportExplicit : Finset ℕ :=
  ([20074] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part001 : ℚ :=
  (1574083890625 : ℚ) / 6341755264883249952

def SurrogateDiagonalTailChunk001Sub000Block087Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20074
    = surrogateDiagTailX0RatChunk001Sub000Block087Part001

theorem surrogateDiagonalTailChunk001Sub000Block087Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part001] using hcert

def TailChunk001Sub000Block087Part002SupportExplicit : Finset ℕ :=
  ([20077] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part002 : ℚ :=
  (7045630721 : ℚ) / 99285274396262400

def SurrogateDiagonalTailChunk001Sub000Block087Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20077
    = surrogateDiagTailX0RatChunk001Sub000Block087Part002

theorem surrogateDiagonalTailChunk001Sub000Block087Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part002] using hcert

def TailChunk001Sub000Block087Part003SupportExplicit : Finset ℕ :=
  ([20078] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part003 : ℚ :=
  (1574711265625 : ℚ) / 6346811981677830642

def SurrogateDiagonalTailChunk001Sub000Block087Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20078
    = surrogateDiagTailX0RatChunk001Sub000Block087Part003

theorem surrogateDiagonalTailChunk001Sub000Block087Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part003] using hcert

def TailChunk001Sub000Block087Part004SupportExplicit : Finset ℕ :=
  ([20081] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part004 : ℚ :=
  (24092302835575 : ℚ) / 366916876042012748928

def SurrogateDiagonalTailChunk001Sub000Block087Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20081
    = surrogateDiagTailX0RatChunk001Sub000Block087Part004

theorem surrogateDiagonalTailChunk001Sub000Block087Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part004] using hcert

def TailChunk001Sub000Block087Part005SupportExplicit : Finset ℕ :=
  ([20082] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part005 : ℚ :=
  (2799553665325 : ℚ) / 5014765022560261248

def SurrogateDiagonalTailChunk001Sub000Block087Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20082
    = surrogateDiagTailX0RatChunk001Sub000Block087Part005

theorem surrogateDiagonalTailChunk001Sub000Block087Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part005] using hcert

def TailChunk001Sub000Block087Part006SupportExplicit : Finset ℕ :=
  ([20083] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part006 : ℚ :=
  (341649649043 : ℚ) / 3444426427536000000

def SurrogateDiagonalTailChunk001Sub000Block087Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20083
    = surrogateDiagTailX0RatChunk001Sub000Block087Part006

theorem surrogateDiagonalTailChunk001Sub000Block087Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part006] using hcert

def TailChunk001Sub000Block087Part007SupportExplicit : Finset ℕ :=
  ([20085] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part007 : ℚ :=
  (722808239575 : ℚ) / 2554288620932431872

def SurrogateDiagonalTailChunk001Sub000Block087Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20085
    = surrogateDiagTailX0RatChunk001Sub000Block087Part007

theorem surrogateDiagonalTailChunk001Sub000Block087Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part007] using hcert

def TailChunk001Sub000Block087Part008SupportExplicit : Finset ℕ :=
  ([20087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part008 : ℚ :=
  (8090915025575 : ℚ) / 124418848624540194816

def SurrogateDiagonalTailChunk001Sub000Block087Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20087
    = surrogateDiagTailX0RatChunk001Sub000Block087Part008

theorem surrogateDiagonalTailChunk001Sub000Block087Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part008] using hcert

def TailChunk001Sub000Block087Part009SupportExplicit : Finset ℕ :=
  ([20089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part009 : ℚ :=
  (6305748765625 : ℚ) / 101792004441103176192

def SurrogateDiagonalTailChunk001Sub000Block087Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20089
    = surrogateDiagTailX0RatChunk001Sub000Block087Part009

theorem surrogateDiagonalTailChunk001Sub000Block087Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part009] using hcert

def TailChunk001Sub000Block087Part010SupportExplicit : Finset ℕ :=
  ([20091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part010 : ℚ :=
  (9448092251 : ℚ) / 62703869543055360

def SurrogateDiagonalTailChunk001Sub000Block087Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20091
    = surrogateDiagTailX0RatChunk001Sub000Block087Part010

theorem surrogateDiagonalTailChunk001Sub000Block087Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part010] using hcert

def TailChunk001Sub000Block087Part011SupportExplicit : Finset ℕ :=
  ([20093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part011 : ℚ :=
  (15531571997 : ℚ) / 241065407392790400

def SurrogateDiagonalTailChunk001Sub000Block087Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20093
    = surrogateDiagTailX0RatChunk001Sub000Block087Part011

theorem surrogateDiagonalTailChunk001Sub000Block087Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part011] using hcert

def TailChunk001Sub000Block087Part012SupportExplicit : Finset ℕ :=
  ([20094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part012 : ℚ :=
  (322064952425 : ℚ) / 483683275181654016

def SurrogateDiagonalTailChunk001Sub000Block087Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20094
    = surrogateDiagTailX0RatChunk001Sub000Block087Part012

theorem surrogateDiagonalTailChunk001Sub000Block087Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part012] using hcert

def TailChunk001Sub000Block087Part013SupportExplicit : Finset ℕ :=
  ([20095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part013 : ℚ :=
  (1009098390625 : ℚ) / 10427653010258375808

def SurrogateDiagonalTailChunk001Sub000Block087Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20095
    = surrogateDiagTailX0RatChunk001Sub000Block087Part013

theorem surrogateDiagonalTailChunk001Sub000Block087Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part013] using hcert

def TailChunk001Sub000Block087Part014SupportExplicit : Finset ℕ :=
  ([20098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part014 : ℚ :=
  (5591943919375 : ℚ) / 18417091442543198208

def SurrogateDiagonalTailChunk001Sub000Block087Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20098
    = surrogateDiagTailX0RatChunk001Sub000Block087Part014

theorem surrogateDiagonalTailChunk001Sub000Block087Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part014] using hcert

def TailChunk001Sub000Block087Part015SupportExplicit : Finset ℕ :=
  ([20099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part015 : ℚ :=
  (327924222533 : ℚ) / 5124203355744000000

def SurrogateDiagonalTailChunk001Sub000Block087Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20099
    = surrogateDiagTailX0RatChunk001Sub000Block087Part015

theorem surrogateDiagonalTailChunk001Sub000Block087Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part015] using hcert

def TailChunk001Sub000Block087Part016SupportExplicit : Finset ℕ :=
  ([20101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part016 : ℚ :=
  (404050201 : ℚ) / 6530268996640800

def SurrogateDiagonalTailChunk001Sub000Block087Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20101
    = surrogateDiagTailX0RatChunk001Sub000Block087Part016

theorem surrogateDiagonalTailChunk001Sub000Block087Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part016] using hcert

def TailChunk001Sub000Block087Part017SupportExplicit : Finset ℕ :=
  ([20103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part017 : ℚ :=
  (448924973197 : ℚ) / 3224824195872000000

def SurrogateDiagonalTailChunk001Sub000Block087Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20103
    = surrogateDiagTailX0RatChunk001Sub000Block087Part017

theorem surrogateDiagonalTailChunk001Sub000Block087Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part017] using hcert

def TailChunk001Sub000Block087Part018SupportExplicit : Finset ℕ :=
  ([20105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part018 : ℚ :=
  (538721675 : ℚ) / 5572496210466816

def SurrogateDiagonalTailChunk001Sub000Block087Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20105
    = surrogateDiagTailX0RatChunk001Sub000Block087Part018

theorem surrogateDiagonalTailChunk001Sub000Block087Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part018] using hcert

def TailChunk001Sub000Block087Part019SupportExplicit : Finset ℕ :=
  ([20107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part019 : ℚ :=
  (6317053890625 : ℚ) / 102157341012430750962

def SurrogateDiagonalTailChunk001Sub000Block087Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20107
    = surrogateDiagTailX0RatChunk001Sub000Block087Part019

theorem surrogateDiagonalTailChunk001Sub000Block087Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part019] using hcert

def TailChunk001Sub000Block087Part020SupportExplicit : Finset ℕ :=
  ([20109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part020 : ℚ :=
  (11229825329725 : ℚ) / 80716911417229235328

def SurrogateDiagonalTailChunk001Sub000Block087Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20109
    = surrogateDiagTailX0RatChunk001Sub000Block087Part020

theorem surrogateDiagonalTailChunk001Sub000Block087Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part020] using hcert

def TailChunk001Sub000Block087Part021SupportExplicit : Finset ℕ :=
  ([20110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part021 : ℚ :=
  (181882793737 : ℚ) / 417937215785011200

def SurrogateDiagonalTailChunk001Sub000Block087Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20110
    = surrogateDiagTailX0RatChunk001Sub000Block087Part021

theorem surrogateDiagonalTailChunk001Sub000Block087Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part021] using hcert

def TailChunk001Sub000Block087Part022SupportExplicit : Finset ℕ :=
  ([20113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part022 : ℚ :=
  (6320824515625 : ℚ) / 102279338122013908992

def SurrogateDiagonalTailChunk001Sub000Block087Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20113
    = surrogateDiagTailX0RatChunk001Sub000Block087Part022

theorem surrogateDiagonalTailChunk001Sub000Block087Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part022] using hcert

def TailChunk001Sub000Block087Part023SupportExplicit : Finset ℕ :=
  ([20114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part023 : ℚ :=
  (438152054675 : ℚ) / 1685394616989253632

def SurrogateDiagonalTailChunk001Sub000Block087Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20114
    = surrogateDiagTailX0RatChunk001Sub000Block087Part023

theorem surrogateDiagonalTailChunk001Sub000Block087Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part023] using hcert

def TailChunk001Sub000Block087Part024SupportExplicit : Finset ℕ :=
  ([20117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block087Part024 : ℚ :=
  (6323338890625 : ℚ) / 102360730210396552992

def SurrogateDiagonalTailChunk001Sub000Block087Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20117
    = surrogateDiagTailX0RatChunk001Sub000Block087Part024

theorem surrogateDiagonalTailChunk001Sub000Block087Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block087Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block087Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block087Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block087Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block087Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block087HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block087Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block087Part000
    + surrogateDiagTailX0RatChunk001Sub000Block087Part001
    + surrogateDiagTailX0RatChunk001Sub000Block087Part002
    + surrogateDiagTailX0RatChunk001Sub000Block087Part003
    + surrogateDiagTailX0RatChunk001Sub000Block087Part004
    + surrogateDiagTailX0RatChunk001Sub000Block087Part005
    + surrogateDiagTailX0RatChunk001Sub000Block087Part006
    + surrogateDiagTailX0RatChunk001Sub000Block087Part007
    + surrogateDiagTailX0RatChunk001Sub000Block087Part008
    + surrogateDiagTailX0RatChunk001Sub000Block087Part009

def surrogateDiagonalTailChunk001Sub000Block087MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block087Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block087Part010
    + surrogateDiagTailX0RatChunk001Sub000Block087Part011
    + surrogateDiagTailX0RatChunk001Sub000Block087Part012
    + surrogateDiagTailX0RatChunk001Sub000Block087Part013
    + surrogateDiagTailX0RatChunk001Sub000Block087Part014
    + surrogateDiagTailX0RatChunk001Sub000Block087Part015
    + surrogateDiagTailX0RatChunk001Sub000Block087Part016
    + surrogateDiagTailX0RatChunk001Sub000Block087Part017
    + surrogateDiagTailX0RatChunk001Sub000Block087Part018
    + surrogateDiagTailX0RatChunk001Sub000Block087Part019

def surrogateDiagonalTailChunk001Sub000Block087TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block087Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block087Part020
    + surrogateDiagTailX0RatChunk001Sub000Block087Part021
    + surrogateDiagTailX0RatChunk001Sub000Block087Part022
    + surrogateDiagTailX0RatChunk001Sub000Block087Part023
    + surrogateDiagTailX0RatChunk001Sub000Block087Part024

def surrogateDiagonalTailChunk001Sub000Block087Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block087HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block087MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block087TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block087 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block087Part000
    + surrogateDiagTailX0RatChunk001Sub000Block087Part001
    + surrogateDiagTailX0RatChunk001Sub000Block087Part002
    + surrogateDiagTailX0RatChunk001Sub000Block087Part003
    + surrogateDiagTailX0RatChunk001Sub000Block087Part004
    + surrogateDiagTailX0RatChunk001Sub000Block087Part005
    + surrogateDiagTailX0RatChunk001Sub000Block087Part006
    + surrogateDiagTailX0RatChunk001Sub000Block087Part007
    + surrogateDiagTailX0RatChunk001Sub000Block087Part008
    + surrogateDiagTailX0RatChunk001Sub000Block087Part009
    + surrogateDiagTailX0RatChunk001Sub000Block087Part010
    + surrogateDiagTailX0RatChunk001Sub000Block087Part011
    + surrogateDiagTailX0RatChunk001Sub000Block087Part012
    + surrogateDiagTailX0RatChunk001Sub000Block087Part013
    + surrogateDiagTailX0RatChunk001Sub000Block087Part014
    + surrogateDiagTailX0RatChunk001Sub000Block087Part015
    + surrogateDiagTailX0RatChunk001Sub000Block087Part016
    + surrogateDiagTailX0RatChunk001Sub000Block087Part017
    + surrogateDiagTailX0RatChunk001Sub000Block087Part018
    + surrogateDiagTailX0RatChunk001Sub000Block087Part019
    + surrogateDiagTailX0RatChunk001Sub000Block087Part020
    + surrogateDiagTailX0RatChunk001Sub000Block087Part021
    + surrogateDiagTailX0RatChunk001Sub000Block087Part022
    + surrogateDiagTailX0RatChunk001Sub000Block087Part023
    + surrogateDiagTailX0RatChunk001Sub000Block087Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block087_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block087Head + surrogateDiagTailX0RatChunk001Sub000Block087Mid + surrogateDiagTailX0RatChunk001Sub000Block087Tail =
      surrogateDiagTailX0RatChunk001Sub000Block087 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block087Head surrogateDiagTailX0RatChunk001Sub000Block087Mid surrogateDiagTailX0RatChunk001Sub000Block087Tail surrogateDiagTailX0RatChunk001Sub000Block087
  ring

def SurrogateDiagonalTailChunk001Sub000Block087HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block087HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block087Head

def SurrogateDiagonalTailChunk001Sub000Block087MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block087MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block087Mid

def SurrogateDiagonalTailChunk001Sub000Block087TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block087TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block087Tail

theorem surrogateDiagonalTailChunk001Sub000Block087_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block087HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block087MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block087TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block087Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block087 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block087HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block087MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block087TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block087Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block087_eq_head_add_mid_add_tail

/-- Block 088 covers tail-support indices [12200,12225) and q from 20118 to 20158. -/

def TailChunk001Sub000Block088Part000SupportExplicit : Finset ℕ :=
  ([20118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part000 : ℚ :=
  (2331401027275 : ℚ) / 2706845259990878208

def SurrogateDiagonalTailChunk001Sub000Block088Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20118
    = surrogateDiagTailX0RatChunk001Sub000Block088Part000

theorem surrogateDiagonalTailChunk001Sub000Block088Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part000] using hcert

def TailChunk001Sub000Block088Part001SupportExplicit : Finset ℕ :=
  ([20119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part001 : ℚ :=
  (130329167129 : ℚ) / 1528032505392000000

def SurrogateDiagonalTailChunk001Sub000Block088Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20119
    = surrogateDiagTailX0RatChunk001Sub000Block088Part001

theorem surrogateDiagonalTailChunk001Sub000Block088Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part001] using hcert

def TailChunk001Sub000Block088Part002SupportExplicit : Finset ℕ :=
  ([20121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part002 : ℚ :=
  (2554332909925 : ℚ) / 16119349973857861632

def SurrogateDiagonalTailChunk001Sub000Block088Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20121
    = surrogateDiagTailX0RatChunk001Sub000Block088Part002

theorem surrogateDiagonalTailChunk001Sub000Block088Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part002] using hcert

def TailChunk001Sub000Block088Part003SupportExplicit : Finset ℕ :=
  ([20122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part003 : ℚ :=
  (2530593025 : ℚ) / 10244217086690592

def SurrogateDiagonalTailChunk001Sub000Block088Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20122
    = surrogateDiagTailX0RatChunk001Sub000Block088Part003

theorem surrogateDiagonalTailChunk001Sub000Block088Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part003] using hcert

def TailChunk001Sub000Block088Part004SupportExplicit : Finset ℕ :=
  ([20123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part004 : ℚ :=
  (6327111390625 : ℚ) / 102482909414244581682

def SurrogateDiagonalTailChunk001Sub000Block088Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20123
    = surrogateDiagTailX0RatChunk001Sub000Block088Part004

theorem surrogateDiagonalTailChunk001Sub000Block088Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part004] using hcert

def TailChunk001Sub000Block088Part005SupportExplicit : Finset ℕ :=
  ([20126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part005 : ℚ :=
  (5980414757575 : ℚ) / 22027407157347207168

def SurrogateDiagonalTailChunk001Sub000Block088Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20126
    = surrogateDiagTailX0RatChunk001Sub000Block088Part005

theorem surrogateDiagonalTailChunk001Sub000Block088Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part005] using hcert

def TailChunk001Sub000Block088Part006SupportExplicit : Finset ℕ :=
  ([20127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part006 : ℚ :=
  (11249940329125 : ℚ) / 81006348729567725568

def SurrogateDiagonalTailChunk001Sub000Block088Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20127
    = surrogateDiagTailX0RatChunk001Sub000Block088Part006

theorem surrogateDiagonalTailChunk001Sub000Block088Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part006] using hcert

def TailChunk001Sub000Block088Part007SupportExplicit : Finset ℕ :=
  ([20129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part007 : ℚ :=
  (6330885015625 : ℚ) / 102605197961577234432

def SurrogateDiagonalTailChunk001Sub000Block088Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20129
    = surrogateDiagTailX0RatChunk001Sub000Block088Part007

theorem surrogateDiagonalTailChunk001Sub000Block088Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part007] using hcert

def TailChunk001Sub000Block088Part008SupportExplicit : Finset ℕ :=
  ([20130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part008 : ℚ :=
  (3582881909 : ℚ) / 2654738841600000

def SurrogateDiagonalTailChunk001Sub000Block088Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20130
    = surrogateDiagTailX0RatChunk001Sub000Block088Part008

theorem surrogateDiagonalTailChunk001Sub000Block088Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part008] using hcert

def TailChunk001Sub000Block088Part009SupportExplicit : Finset ℕ :=
  ([20131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part009 : ℚ :=
  (27610738871 : ℚ) / 421738346803200000

def SurrogateDiagonalTailChunk001Sub000Block088Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20131
    = surrogateDiagTailX0RatChunk001Sub000Block088Part009

theorem surrogateDiagonalTailChunk001Sub000Block088Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part009] using hcert

def TailChunk001Sub000Block088Part010SupportExplicit : Finset ℕ :=
  ([20134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part010 : ℚ :=
  (1583507640625 : ℚ) / 6417924027399061842

def SurrogateDiagonalTailChunk001Sub000Block088Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20134
    = surrogateDiagTailX0RatChunk001Sub000Block088Part010

theorem surrogateDiagonalTailChunk001Sub000Block088Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part010] using hcert

def TailChunk001Sub000Block088Part011SupportExplicit : Finset ℕ :=
  ([20135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part011 : ℚ :=
  (337706796875 : ℚ) / 3503649625446807936

def SurrogateDiagonalTailChunk001Sub000Block088Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20135
    = surrogateDiagTailX0RatChunk001Sub000Block088Part011

theorem surrogateDiagonalTailChunk001Sub000Block088Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part011] using hcert

def TailChunk001Sub000Block088Part012SupportExplicit : Finset ℕ :=
  ([20137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part012 : ℚ :=
  (11010881635175 : ℚ) / 148869480484491116544

def SurrogateDiagonalTailChunk001Sub000Block088Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20137
    = surrogateDiagTailX0RatChunk001Sub000Block088Part012

theorem surrogateDiagonalTailChunk001Sub000Block088Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part012] using hcert

def TailChunk001Sub000Block088Part013SupportExplicit : Finset ℕ :=
  ([20138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part013 : ℚ :=
  (1584136890625 : ℚ) / 6423026222538192672

def SurrogateDiagonalTailChunk001Sub000Block088Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20138
    = surrogateDiagTailX0RatChunk001Sub000Block088Part013

theorem surrogateDiagonalTailChunk001Sub000Block088Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part013] using hcert

def TailChunk001Sub000Block088Part014SupportExplicit : Finset ℕ :=
  ([20141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part014 : ℚ :=
  (84575554411 : ℚ) / 1121737423624200000

def SurrogateDiagonalTailChunk001Sub000Block088Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20141
    = surrogateDiagTailX0RatChunk001Sub000Block088Part014

theorem surrogateDiagonalTailChunk001Sub000Block088Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part014] using hcert

def TailChunk001Sub000Block088Part015SupportExplicit : Finset ℕ :=
  ([20143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part015 : ℚ :=
  (6339694515625 : ℚ) / 102890963496400513362

def SurrogateDiagonalTailChunk001Sub000Block088Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20143
    = surrogateDiagTailX0RatChunk001Sub000Block088Part015

theorem surrogateDiagonalTailChunk001Sub000Block088Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part015] using hcert

def TailChunk001Sub000Block088Part016SupportExplicit : Finset ℕ :=
  ([20145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part016 : ℚ :=
  (6742343349325 : ℚ) / 24845351667281952768

def SurrogateDiagonalTailChunk001Sub000Block088Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20145
    = surrogateDiagTailX0RatChunk001Sub000Block088Part016

theorem surrogateDiagonalTailChunk001Sub000Block088Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part016] using hcert

def TailChunk001Sub000Block088Part017SupportExplicit : Finset ℕ :=
  ([20146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part017 : ℚ :=
  (307098099175 : ℚ) / 866058885829777608

def SurrogateDiagonalTailChunk001Sub000Block088Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20146
    = surrogateDiagTailX0RatChunk001Sub000Block088Part017

theorem surrogateDiagonalTailChunk001Sub000Block088Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part017] using hcert

def TailChunk001Sub000Block088Part018SupportExplicit : Finset ℕ :=
  ([20147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part018 : ℚ :=
  (6342212640625 : ℚ) / 102972720316760566482

def SurrogateDiagonalTailChunk001Sub000Block088Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20147
    = surrogateDiagTailX0RatChunk001Sub000Block088Part018

theorem surrogateDiagonalTailChunk001Sub000Block088Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part018] using hcert

def TailChunk001Sub000Block088Part019SupportExplicit : Finset ℕ :=
  ([20149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part019 : ℚ :=
  (6343471890625 : ℚ) / 103013616993143653152

def SurrogateDiagonalTailChunk001Sub000Block088Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20149
    = surrogateDiagTailX0RatChunk001Sub000Block088Part019

theorem surrogateDiagonalTailChunk001Sub000Block088Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part019] using hcert

def TailChunk001Sub000Block088Part020SupportExplicit : Finset ℕ :=
  ([20153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part020 : ℚ :=
  (19157281303225 : ℚ) / 222328439034605071488

def SurrogateDiagonalTailChunk001Sub000Block088Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20153
    = surrogateDiagTailX0RatChunk001Sub000Block088Part020

theorem surrogateDiagonalTailChunk001Sub000Block088Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part020] using hcert

def TailChunk001Sub000Block088Part021SupportExplicit : Finset ℕ :=
  ([20154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part021 : ℚ :=
  (881247477925 : ℚ) / 1271773049298069792

def SurrogateDiagonalTailChunk001Sub000Block088Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20154
    = surrogateDiagTailX0RatChunk001Sub000Block088Part021

theorem surrogateDiagonalTailChunk001Sub000Block088Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part021] using hcert

def TailChunk001Sub000Block088Part022SupportExplicit : Finset ℕ :=
  ([20155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part022 : ℚ :=
  (7556401557275 : ℚ) / 71348574319416705024

def SurrogateDiagonalTailChunk001Sub000Block088Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20155
    = surrogateDiagTailX0RatChunk001Sub000Block088Part022

theorem surrogateDiagonalTailChunk001Sub000Block088Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part022] using hcert

def TailChunk001Sub000Block088Part023SupportExplicit : Finset ℕ :=
  ([20157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part023 : ℚ :=
  (11283505328125 : ℚ) / 81490473178171540608

def SurrogateDiagonalTailChunk001Sub000Block088Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20157
    = surrogateDiagTailX0RatChunk001Sub000Block088Part023

theorem surrogateDiagonalTailChunk001Sub000Block088Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part023] using hcert

def TailChunk001Sub000Block088Part024SupportExplicit : Finset ℕ :=
  ([20158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block088Part024 : ℚ :=
  (1587285015625 : ℚ) / 6448582845611796882

def SurrogateDiagonalTailChunk001Sub000Block088Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20158
    = surrogateDiagTailX0RatChunk001Sub000Block088Part024

theorem surrogateDiagonalTailChunk001Sub000Block088Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block088Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block088Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block088Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block088Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block088Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block088HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block088Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block088Part000
    + surrogateDiagTailX0RatChunk001Sub000Block088Part001
    + surrogateDiagTailX0RatChunk001Sub000Block088Part002
    + surrogateDiagTailX0RatChunk001Sub000Block088Part003
    + surrogateDiagTailX0RatChunk001Sub000Block088Part004
    + surrogateDiagTailX0RatChunk001Sub000Block088Part005
    + surrogateDiagTailX0RatChunk001Sub000Block088Part006
    + surrogateDiagTailX0RatChunk001Sub000Block088Part007
    + surrogateDiagTailX0RatChunk001Sub000Block088Part008
    + surrogateDiagTailX0RatChunk001Sub000Block088Part009

def surrogateDiagonalTailChunk001Sub000Block088MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block088Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block088Part010
    + surrogateDiagTailX0RatChunk001Sub000Block088Part011
    + surrogateDiagTailX0RatChunk001Sub000Block088Part012
    + surrogateDiagTailX0RatChunk001Sub000Block088Part013
    + surrogateDiagTailX0RatChunk001Sub000Block088Part014
    + surrogateDiagTailX0RatChunk001Sub000Block088Part015
    + surrogateDiagTailX0RatChunk001Sub000Block088Part016
    + surrogateDiagTailX0RatChunk001Sub000Block088Part017
    + surrogateDiagTailX0RatChunk001Sub000Block088Part018
    + surrogateDiagTailX0RatChunk001Sub000Block088Part019

def surrogateDiagonalTailChunk001Sub000Block088TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block088Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block088Part020
    + surrogateDiagTailX0RatChunk001Sub000Block088Part021
    + surrogateDiagTailX0RatChunk001Sub000Block088Part022
    + surrogateDiagTailX0RatChunk001Sub000Block088Part023
    + surrogateDiagTailX0RatChunk001Sub000Block088Part024

def surrogateDiagonalTailChunk001Sub000Block088Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block088HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block088MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block088TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block088 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block088Part000
    + surrogateDiagTailX0RatChunk001Sub000Block088Part001
    + surrogateDiagTailX0RatChunk001Sub000Block088Part002
    + surrogateDiagTailX0RatChunk001Sub000Block088Part003
    + surrogateDiagTailX0RatChunk001Sub000Block088Part004
    + surrogateDiagTailX0RatChunk001Sub000Block088Part005
    + surrogateDiagTailX0RatChunk001Sub000Block088Part006
    + surrogateDiagTailX0RatChunk001Sub000Block088Part007
    + surrogateDiagTailX0RatChunk001Sub000Block088Part008
    + surrogateDiagTailX0RatChunk001Sub000Block088Part009
    + surrogateDiagTailX0RatChunk001Sub000Block088Part010
    + surrogateDiagTailX0RatChunk001Sub000Block088Part011
    + surrogateDiagTailX0RatChunk001Sub000Block088Part012
    + surrogateDiagTailX0RatChunk001Sub000Block088Part013
    + surrogateDiagTailX0RatChunk001Sub000Block088Part014
    + surrogateDiagTailX0RatChunk001Sub000Block088Part015
    + surrogateDiagTailX0RatChunk001Sub000Block088Part016
    + surrogateDiagTailX0RatChunk001Sub000Block088Part017
    + surrogateDiagTailX0RatChunk001Sub000Block088Part018
    + surrogateDiagTailX0RatChunk001Sub000Block088Part019
    + surrogateDiagTailX0RatChunk001Sub000Block088Part020
    + surrogateDiagTailX0RatChunk001Sub000Block088Part021
    + surrogateDiagTailX0RatChunk001Sub000Block088Part022
    + surrogateDiagTailX0RatChunk001Sub000Block088Part023
    + surrogateDiagTailX0RatChunk001Sub000Block088Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block088_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block088Head + surrogateDiagTailX0RatChunk001Sub000Block088Mid + surrogateDiagTailX0RatChunk001Sub000Block088Tail =
      surrogateDiagTailX0RatChunk001Sub000Block088 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block088Head surrogateDiagTailX0RatChunk001Sub000Block088Mid surrogateDiagTailX0RatChunk001Sub000Block088Tail surrogateDiagTailX0RatChunk001Sub000Block088
  ring

def SurrogateDiagonalTailChunk001Sub000Block088HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block088HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block088Head

def SurrogateDiagonalTailChunk001Sub000Block088MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block088MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block088Mid

def SurrogateDiagonalTailChunk001Sub000Block088TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block088TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block088Tail

theorem surrogateDiagonalTailChunk001Sub000Block088_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block088HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block088MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block088TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block088Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block088 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block088HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block088MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block088TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block088Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block088_eq_head_add_mid_add_tail

/-- Block 089 covers tail-support indices [12225,12250) and q from 20159 to 20198. -/

def TailChunk001Sub000Block089Part000SupportExplicit : Finset ℕ :=
  ([20159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part000 : ℚ :=
  (918824103631 : ℚ) / 13255628730923059200

def SurrogateDiagonalTailChunk001Sub000Block089Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20159
    = surrogateDiagTailX0RatChunk001Sub000Block089Part000

theorem surrogateDiagonalTailChunk001Sub000Block089Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part000] using hcert

def TailChunk001Sub000Block089Part001SupportExplicit : Finset ℕ :=
  ([20161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part001 : ℚ :=
  (10161648025 : ℚ) / 165214804689027072

def SurrogateDiagonalTailChunk001Sub000Block089Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20161
    = surrogateDiagTailX0RatChunk001Sub000Block089Part001

theorem surrogateDiagonalTailChunk001Sub000Block089Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part001] using hcert

def TailChunk001Sub000Block089Part002SupportExplicit : Finset ℕ :=
  ([20162] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part002 : ℚ :=
  (961088408625 : ℚ) / 3354612539366309888

def SurrogateDiagonalTailChunk001Sub000Block089Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20162
    = surrogateDiagTailX0RatChunk001Sub000Block089Part002

theorem surrogateDiagonalTailChunk001Sub000Block089Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part002] using hcert

def TailChunk001Sub000Block089Part003SupportExplicit : Finset ℕ :=
  ([20163] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part003 : ℚ :=
  (54306001747 : ℚ) / 247634924057395200

def SurrogateDiagonalTailChunk001Sub000Block089Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20163
    = surrogateDiagTailX0RatChunk001Sub000Block089Part003

theorem surrogateDiagonalTailChunk001Sub000Block089Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part003] using hcert

def TailChunk001Sub000Block089Part004SupportExplicit : Finset ℕ :=
  ([20165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part004 : ℚ :=
  (2028229341125 : ℚ) / 18284448358754942976

def SurrogateDiagonalTailChunk001Sub000Block089Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20165
    = surrogateDiagTailX0RatChunk001Sub000Block089Part004

theorem surrogateDiagonalTailChunk001Sub000Block089Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part004] using hcert

def TailChunk001Sub000Block089Part005SupportExplicit : Finset ℕ :=
  ([20166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part005 : ℚ :=
  (70583786669 : ℚ) / 101984447338905600

def SurrogateDiagonalTailChunk001Sub000Block089Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20166
    = surrogateDiagTailX0RatChunk001Sub000Block089Part005

theorem surrogateDiagonalTailChunk001Sub000Block089Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part005] using hcert

def TailChunk001Sub000Block089Part006SupportExplicit : Finset ℕ :=
  ([20167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part006 : ℚ :=
  (1994223198775 : ℚ) / 21259950780340242432

def SurrogateDiagonalTailChunk001Sub000Block089Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20167
    = surrogateDiagTailX0RatChunk001Sub000Block089Part006

theorem surrogateDiagonalTailChunk001Sub000Block089Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part006] using hcert

def TailChunk001Sub000Block089Part007SupportExplicit : Finset ℕ :=
  ([20170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part007 : ℚ :=
  (653464224475 : ℚ) / 1510535357156818944

def SurrogateDiagonalTailChunk001Sub000Block089Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20170
    = surrogateDiagTailX0RatChunk001Sub000Block089Part007

theorem surrogateDiagonalTailChunk001Sub000Block089Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part007] using hcert

def TailChunk001Sub000Block089Part008SupportExplicit : Finset ℕ :=
  ([20171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part008 : ℚ :=
  (11706682094975 : ℚ) / 172466206612654040064

def SurrogateDiagonalTailChunk001Sub000Block089Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20171
    = surrogateDiagTailX0RatChunk001Sub000Block089Part008

theorem surrogateDiagonalTailChunk001Sub000Block089Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part008] using hcert

def TailChunk001Sub000Block089Part009SupportExplicit : Finset ℕ :=
  ([20173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part009 : ℚ :=
  (6358592640625 : ℚ) / 103505327895602041632

def SurrogateDiagonalTailChunk001Sub000Block089Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20173
    = surrogateDiagTailX0RatChunk001Sub000Block089Part009

theorem surrogateDiagonalTailChunk001Sub000Block089Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part009] using hcert

def TailChunk001Sub000Block089Part010SupportExplicit : Finset ℕ :=
  ([20174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part010 : ℚ :=
  (19210048301 : ℚ) / 41136065568000000

def SurrogateDiagonalTailChunk001Sub000Block089Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20174
    = surrogateDiagTailX0RatChunk001Sub000Block089Part010

theorem surrogateDiagonalTailChunk001Sub000Block089Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part010] using hcert

def TailChunk001Sub000Block089Part011SupportExplicit : Finset ℕ :=
  ([20177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part011 : ℚ :=
  (6361114515625 : ℚ) / 103587450535933059072

def SurrogateDiagonalTailChunk001Sub000Block089Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20177
    = surrogateDiagTailX0RatChunk001Sub000Block089Part011

theorem surrogateDiagonalTailChunk001Sub000Block089Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part011] using hcert

def TailChunk001Sub000Block089Part012SupportExplicit : Finset ℕ :=
  ([20179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part012 : ℚ :=
  (5693957999125 : ℚ) / 81056072076388073472

def SurrogateDiagonalTailChunk001Sub000Block089Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20179
    = surrogateDiagTailX0RatChunk001Sub000Block089Part012

theorem surrogateDiagonalTailChunk001Sub000Block089Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part012] using hcert

def TailChunk001Sub000Block089Part013SupportExplicit : Finset ℕ :=
  ([20182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part013 : ℚ :=
  (2545707025 : ℚ) / 10366962203455122

def SurrogateDiagonalTailChunk001Sub000Block089Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20182
    = surrogateDiagTailX0RatChunk001Sub000Block089Part013

theorem surrogateDiagonalTailChunk001Sub000Block089Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part013] using hcert

def TailChunk001Sub000Block089Part014SupportExplicit : Finset ℕ :=
  ([20183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part014 : ℚ :=
  (6364898265625 : ℚ) / 103710726111772439922

def SurrogateDiagonalTailChunk001Sub000Block089Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20183
    = surrogateDiagTailX0RatChunk001Sub000Block089Part014

theorem surrogateDiagonalTailChunk001Sub000Block089Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part014] using hcert

def TailChunk001Sub000Block089Part015SupportExplicit : Finset ℕ :=
  ([20185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part015 : ℚ :=
  (194640760717 : ℚ) / 1531545495721574400

def SurrogateDiagonalTailChunk001Sub000Block089Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20185
    = surrogateDiagTailX0RatChunk001Sub000Block089Part015

theorem surrogateDiagonalTailChunk001Sub000Block089Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part015] using hcert

def TailChunk001Sub000Block089Part016SupportExplicit : Finset ℕ :=
  ([20186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part016 : ℚ :=
  (1591697640625 : ℚ) / 6484490150676954912

def SurrogateDiagonalTailChunk001Sub000Block089Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20186
    = surrogateDiagTailX0RatChunk001Sub000Block089Part016

theorem surrogateDiagonalTailChunk001Sub000Block089Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part016] using hcert

def TailChunk001Sub000Block089Part017SupportExplicit : Finset ℕ :=
  ([20189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part017 : ℚ :=
  (11067849247925 : ℚ) / 150414157369357369344

def SurrogateDiagonalTailChunk001Sub000Block089Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20189
    = surrogateDiagTailX0RatChunk001Sub000Block089Part017

theorem surrogateDiagonalTailChunk001Sub000Block089Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part017] using hcert

def TailChunk001Sub000Block089Part018SupportExplicit : Finset ℕ :=
  ([20190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part018 : ℚ :=
  (2599530935425 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk001Sub000Block089Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20190
    = surrogateDiagTailX0RatChunk001Sub000Block089Part018

theorem surrogateDiagonalTailChunk001Sub000Block089Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part018] using hcert

def TailChunk001Sub000Block089Part019SupportExplicit : Finset ℕ :=
  ([20191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part019 : ℚ :=
  (5470743293 : ℚ) / 85403389262400000

def SurrogateDiagonalTailChunk001Sub000Block089Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20191
    = surrogateDiagTailX0RatChunk001Sub000Block089Part019

theorem surrogateDiagonalTailChunk001Sub000Block089Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part019] using hcert

def TailChunk001Sub000Block089Part020SupportExplicit : Finset ℕ :=
  ([20193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part020 : ℚ :=
  (387061932475 : ℚ) / 2633203145492914176

def SurrogateDiagonalTailChunk001Sub000Block089Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20193
    = surrogateDiagTailX0RatChunk001Sub000Block089Part020

theorem surrogateDiagonalTailChunk001Sub000Block089Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part020] using hcert

def TailChunk001Sub000Block089Part021SupportExplicit : Finset ℕ :=
  ([20194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part021 : ℚ :=
  (165080604575 : ℚ) / 598840995182826528

def SurrogateDiagonalTailChunk001Sub000Block089Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20194
    = surrogateDiagTailX0RatChunk001Sub000Block089Part021

theorem surrogateDiagonalTailChunk001Sub000Block089Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part021] using hcert

def TailChunk001Sub000Block089Part022SupportExplicit : Finset ℕ :=
  ([20195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part022 : ℚ :=
  (13155056475775 : ℚ) / 91319128763859468288

def SurrogateDiagonalTailChunk001Sub000Block089Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20195
    = surrogateDiagTailX0RatChunk001Sub000Block089Part022

theorem surrogateDiagonalTailChunk001Sub000Block089Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part022] using hcert

def TailChunk001Sub000Block089Part023SupportExplicit : Finset ℕ :=
  ([20197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part023 : ℚ :=
  (856602175675 : ℚ) / 12366624729005645184

def SurrogateDiagonalTailChunk001Sub000Block089Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20197
    = surrogateDiagTailX0RatChunk001Sub000Block089Part023

theorem surrogateDiagonalTailChunk001Sub000Block089Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part023] using hcert

def TailChunk001Sub000Block089Part024SupportExplicit : Finset ℕ :=
  ([20198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub000Block089Part024 : ℚ :=
  (1593590640625 : ℚ) / 6499924812465499602

def SurrogateDiagonalTailChunk001Sub000Block089Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 20198
    = surrogateDiagTailX0RatChunk001Sub000Block089Part024

theorem surrogateDiagonalTailChunk001Sub000Block089Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub000Block089Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub000Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub000Block089Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub000Block089Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub000Block089Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub000Block089Part024] using hcert

def surrogateDiagonalTailChunk001Sub000Block089HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block089Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block089Part000
    + surrogateDiagTailX0RatChunk001Sub000Block089Part001
    + surrogateDiagTailX0RatChunk001Sub000Block089Part002
    + surrogateDiagTailX0RatChunk001Sub000Block089Part003
    + surrogateDiagTailX0RatChunk001Sub000Block089Part004
    + surrogateDiagTailX0RatChunk001Sub000Block089Part005
    + surrogateDiagTailX0RatChunk001Sub000Block089Part006
    + surrogateDiagTailX0RatChunk001Sub000Block089Part007
    + surrogateDiagTailX0RatChunk001Sub000Block089Part008
    + surrogateDiagTailX0RatChunk001Sub000Block089Part009

def surrogateDiagonalTailChunk001Sub000Block089MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block089Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block089Part010
    + surrogateDiagTailX0RatChunk001Sub000Block089Part011
    + surrogateDiagTailX0RatChunk001Sub000Block089Part012
    + surrogateDiagTailX0RatChunk001Sub000Block089Part013
    + surrogateDiagTailX0RatChunk001Sub000Block089Part014
    + surrogateDiagTailX0RatChunk001Sub000Block089Part015
    + surrogateDiagTailX0RatChunk001Sub000Block089Part016
    + surrogateDiagTailX0RatChunk001Sub000Block089Part017
    + surrogateDiagTailX0RatChunk001Sub000Block089Part018
    + surrogateDiagTailX0RatChunk001Sub000Block089Part019

def surrogateDiagonalTailChunk001Sub000Block089TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub000Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub000Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub000Block089Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block089Part020
    + surrogateDiagTailX0RatChunk001Sub000Block089Part021
    + surrogateDiagTailX0RatChunk001Sub000Block089Part022
    + surrogateDiagTailX0RatChunk001Sub000Block089Part023
    + surrogateDiagTailX0RatChunk001Sub000Block089Part024

def surrogateDiagonalTailChunk001Sub000Block089Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub000Block089HeadSum X0
    + surrogateDiagonalTailChunk001Sub000Block089MidSum X0
    + surrogateDiagonalTailChunk001Sub000Block089TailSum X0

def surrogateDiagTailX0RatChunk001Sub000Block089 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub000Block089Part000
    + surrogateDiagTailX0RatChunk001Sub000Block089Part001
    + surrogateDiagTailX0RatChunk001Sub000Block089Part002
    + surrogateDiagTailX0RatChunk001Sub000Block089Part003
    + surrogateDiagTailX0RatChunk001Sub000Block089Part004
    + surrogateDiagTailX0RatChunk001Sub000Block089Part005
    + surrogateDiagTailX0RatChunk001Sub000Block089Part006
    + surrogateDiagTailX0RatChunk001Sub000Block089Part007
    + surrogateDiagTailX0RatChunk001Sub000Block089Part008
    + surrogateDiagTailX0RatChunk001Sub000Block089Part009
    + surrogateDiagTailX0RatChunk001Sub000Block089Part010
    + surrogateDiagTailX0RatChunk001Sub000Block089Part011
    + surrogateDiagTailX0RatChunk001Sub000Block089Part012
    + surrogateDiagTailX0RatChunk001Sub000Block089Part013
    + surrogateDiagTailX0RatChunk001Sub000Block089Part014
    + surrogateDiagTailX0RatChunk001Sub000Block089Part015
    + surrogateDiagTailX0RatChunk001Sub000Block089Part016
    + surrogateDiagTailX0RatChunk001Sub000Block089Part017
    + surrogateDiagTailX0RatChunk001Sub000Block089Part018
    + surrogateDiagTailX0RatChunk001Sub000Block089Part019
    + surrogateDiagTailX0RatChunk001Sub000Block089Part020
    + surrogateDiagTailX0RatChunk001Sub000Block089Part021
    + surrogateDiagTailX0RatChunk001Sub000Block089Part022
    + surrogateDiagTailX0RatChunk001Sub000Block089Part023
    + surrogateDiagTailX0RatChunk001Sub000Block089Part024

theorem surrogateDiagTailX0RatChunk001Sub000Block089_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub000Block089Head + surrogateDiagTailX0RatChunk001Sub000Block089Mid + surrogateDiagTailX0RatChunk001Sub000Block089Tail =
      surrogateDiagTailX0RatChunk001Sub000Block089 := by
  unfold surrogateDiagTailX0RatChunk001Sub000Block089Head surrogateDiagTailX0RatChunk001Sub000Block089Mid surrogateDiagTailX0RatChunk001Sub000Block089Tail surrogateDiagTailX0RatChunk001Sub000Block089
  ring

def SurrogateDiagonalTailChunk001Sub000Block089HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block089HeadSum X0 = surrogateDiagTailX0RatChunk001Sub000Block089Head

def SurrogateDiagonalTailChunk001Sub000Block089MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block089MidSum X0 = surrogateDiagTailX0RatChunk001Sub000Block089Mid

def SurrogateDiagonalTailChunk001Sub000Block089TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub000Block089TailSum X0 = surrogateDiagTailX0RatChunk001Sub000Block089Tail

theorem surrogateDiagonalTailChunk001Sub000Block089_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub000Block089HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub000Block089MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub000Block089TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub000Block089Sum X0 = surrogateDiagTailX0RatChunk001Sub000Block089 := by
  unfold SurrogateDiagonalTailChunk001Sub000Block089HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub000Block089MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub000Block089TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub000Block089Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub000Block089_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
