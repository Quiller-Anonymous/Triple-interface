import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [62,63). -/

/- Block 062 covers tail-support indices [1550,1575) and q from 2599 to 2638. -/

def TailChunk000Sub000Block062Part000SupportExplicit : Finset ℕ :=
  ([2599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part000 : ℚ :=
  (33315989925 : ℚ) / 3840417421524992

def SurrogateDiagonalTailChunk000Sub000Block062Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2599
    = surrogateDiagTailX0RatChunk000Sub000Block062Part000

theorem surrogateDiagonalTailChunk000Sub000Block062Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part000] using hcert

def TailChunk000Sub000Block062Part001SupportExplicit : Finset ℕ :=
  ([2602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part001 : ℚ :=
  (8457927197 : ℚ) / 142833561000000

def SurrogateDiagonalTailChunk000Sub000Block062Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2602
    = surrogateDiagTailX0RatChunk000Sub000Block062Part001

theorem surrogateDiagonalTailChunk000Sub000Block062Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part001] using hcert

def TailChunk000Sub000Block062Part002SupportExplicit : Finset ℕ :=
  ([2603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part002 : ℚ :=
  (265095321475 : ℚ) / 29933069776551936

def SurrogateDiagonalTailChunk000Sub000Block062Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2603
    = surrogateDiagTailX0RatChunk000Sub000Block062Part002

theorem surrogateDiagonalTailChunk000Sub000Block062Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part002] using hcert

def TailChunk000Sub000Block062Part003SupportExplicit : Finset ℕ :=
  ([2605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part003 : ℚ :=
  (1354767899 : ℚ) / 93607402536960

def SurrogateDiagonalTailChunk000Sub000Block062Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2605
    = surrogateDiagTailX0RatChunk000Sub000Block062Part003

theorem surrogateDiagonalTailChunk000Sub000Block062Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part003] using hcert

def TailChunk000Sub000Block062Part004SupportExplicit : Finset ℕ :=
  ([2606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part004 : ℚ :=
  (212098789325 : ℚ) / 3592864181170404

def SurrogateDiagonalTailChunk000Sub000Block062Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2606
    = surrogateDiagTailX0RatChunk000Sub000Block062Part004

theorem surrogateDiagonalTailChunk000Sub000Block062Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part004] using hcert

def TailChunk000Sub000Block062Part005SupportExplicit : Finset ℕ :=
  ([2607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part005 : ℚ :=
  (778353041 : ℚ) / 22783051699200

def SurrogateDiagonalTailChunk000Sub000Block062Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2607
    = surrogateDiagTailX0RatChunk000Sub000Block062Part005

theorem surrogateDiagonalTailChunk000Sub000Block062Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part005] using hcert

def TailChunk000Sub000Block062Part006SupportExplicit : Finset ℕ :=
  ([2609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part006 : ℚ :=
  (850689952975 : ℚ) / 115679714238824448

def SurrogateDiagonalTailChunk000Sub000Block062Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2609
    = surrogateDiagTailX0RatChunk000Sub000Block062Part006

theorem surrogateDiagonalTailChunk000Sub000Block062Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part006] using hcert

def TailChunk000Sub000Block062Part007SupportExplicit : Finset ℕ :=
  ([2611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part007 : ℚ :=
  (359939215025 : ℚ) / 31029417601311744

def SurrogateDiagonalTailChunk000Sub000Block062Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2611
    = surrogateDiagTailX0RatChunk000Sub000Block062Part007

theorem surrogateDiagonalTailChunk000Sub000Block062Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part007] using hcert

def TailChunk000Sub000Block062Part008SupportExplicit : Finset ℕ :=
  ([2613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part008 : ℚ :=
  (43323877475 : ℚ) / 1431050246258688

def SurrogateDiagonalTailChunk000Sub000Block062Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2613
    = surrogateDiagTailX0RatChunk000Sub000Block062Part008

theorem surrogateDiagonalTailChunk000Sub000Block062Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part008] using hcert

def TailChunk000Sub000Block062Part009SupportExplicit : Finset ℕ :=
  ([2614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part009 : ℚ :=
  (213403006325 : ℚ) / 3637220004161124

def SurrogateDiagonalTailChunk000Sub000Block062Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2614
    = surrogateDiagTailX0RatChunk000Sub000Block062Part009

theorem surrogateDiagonalTailChunk000Sub000Block062Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part009] using hcert

def TailChunk000Sub000Block062Part010SupportExplicit : Finset ℕ :=
  ([2615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part010 : ℚ :=
  (12325148725 : ℚ) / 880146723105792

def SurrogateDiagonalTailChunk000Sub000Block062Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2615
    = surrogateDiagTailX0RatChunk000Sub000Block062Part010

theorem surrogateDiagonalTailChunk000Sub000Block062Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part010] using hcert

def TailChunk000Sub000Block062Part011SupportExplicit : Finset ℕ :=
  ([2617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part011 : ℚ :=
  (107010765625 : ℚ) / 29276410376212992

def SurrogateDiagonalTailChunk000Sub000Block062Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2617
    = surrogateDiagTailX0RatChunk000Sub000Block062Part011

theorem surrogateDiagonalTailChunk000Sub000Block062Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part011] using hcert

def TailChunk000Sub000Block062Part012SupportExplicit : Finset ℕ :=
  ([2618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part012 : ℚ :=
  (1241745607 : ℚ) / 8495164293120

def SurrogateDiagonalTailChunk000Sub000Block062Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2618
    = surrogateDiagTailX0RatChunk000Sub000Block062Part012

theorem surrogateDiagonalTailChunk000Sub000Block062Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part012] using hcert

def TailChunk000Sub000Block062Part013SupportExplicit : Finset ℕ :=
  ([2621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part013 : ℚ :=
  (34341335359 : ℚ) / 4712941135747200

def SurrogateDiagonalTailChunk000Sub000Block062Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2621
    = surrogateDiagTailX0RatChunk000Sub000Block062Part013

theorem surrogateDiagonalTailChunk000Sub000Block062Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part013] using hcert

def TailChunk000Sub000Block062Part014SupportExplicit : Finset ℕ :=
  ([2622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part014 : ℚ :=
  (20720445925 : ℚ) / 81987253691904

def SurrogateDiagonalTailChunk000Sub000Block062Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2622
    = surrogateDiagTailX0RatChunk000Sub000Block062Part014

theorem surrogateDiagonalTailChunk000Sub000Block062Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part014] using hcert

def TailChunk000Sub000Block062Part015SupportExplicit : Finset ℕ :=
  ([2623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part015 : ℚ :=
  (16498867667 : ℚ) / 2016782283801600

def SurrogateDiagonalTailChunk000Sub000Block062Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2623
    = surrogateDiagTailX0RatChunk000Sub000Block062Part015

theorem surrogateDiagonalTailChunk000Sub000Block062Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part015] using hcert

def TailChunk000Sub000Block062Part016SupportExplicit : Finset ℕ :=
  ([2626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part016 : ℚ :=
  (1046780341 : ℚ) / 13826764800000

def SurrogateDiagonalTailChunk000Sub000Block062Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2626
    = surrogateDiagTailX0RatChunk000Sub000Block062Part016

theorem surrogateDiagonalTailChunk000Sub000Block062Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part016] using hcert

def TailChunk000Sub000Block062Part017SupportExplicit : Finset ℕ :=
  ([2627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part017 : ℚ :=
  (4719211219 : ℚ) / 576223509657600

def SurrogateDiagonalTailChunk000Sub000Block062Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2627
    = surrogateDiagTailX0RatChunk000Sub000Block062Part017

theorem surrogateDiagonalTailChunk000Sub000Block062Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part017] using hcert

def TailChunk000Sub000Block062Part018SupportExplicit : Finset ℕ :=
  ([2629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part018 : ℚ :=
  (2583469731 : ℚ) / 267432037045600

def SurrogateDiagonalTailChunk000Sub000Block062Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2629
    = surrogateDiagTailX0RatChunk000Sub000Block062Part018

theorem surrogateDiagonalTailChunk000Sub000Block062Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part018] using hcert

def TailChunk000Sub000Block062Part019SupportExplicit : Finset ℕ :=
  ([2630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part019 : ℚ :=
  (170121504575 : ℚ) / 1508141163439104

def SurrogateDiagonalTailChunk000Sub000Block062Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2630
    = surrogateDiagTailX0RatChunk000Sub000Block062Part019

theorem surrogateDiagonalTailChunk000Sub000Block062Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part019] using hcert

def TailChunk000Sub000Block062Part020SupportExplicit : Finset ℕ :=
  ([2631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part020 : ℚ :=
  (384351031075 : ℚ) / 23559347942443008

def SurrogateDiagonalTailChunk000Sub000Block062Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2631
    = surrogateDiagTailX0RatChunk000Sub000Block062Part020

theorem surrogateDiagonalTailChunk000Sub000Block062Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part020] using hcert

def TailChunk000Sub000Block062Part021SupportExplicit : Finset ℕ :=
  ([2633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part021 : ℚ :=
  (866412807775 : ℚ) / 119997002791077888

def SurrogateDiagonalTailChunk000Sub000Block062Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2633
    = surrogateDiagTailX0RatChunk000Sub000Block062Part021

theorem surrogateDiagonalTailChunk000Sub000Block062Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part021] using hcert

def TailChunk000Sub000Block062Part022SupportExplicit : Finset ℕ :=
  ([2634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part022 : ℚ :=
  (19225975 : ℚ) / 98144320896

def SurrogateDiagonalTailChunk000Sub000Block062Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2634
    = surrogateDiagTailX0RatChunk000Sub000Block062Part022

theorem surrogateDiagonalTailChunk000Sub000Block062Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part022] using hcert

def TailChunk000Sub000Block062Part023SupportExplicit : Finset ℕ :=
  ([2635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part023 : ℚ :=
  (12602771609 : ℚ) / 679613143449600

def SurrogateDiagonalTailChunk000Sub000Block062Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2635
    = surrogateDiagTailX0RatChunk000Sub000Block062Part023

theorem surrogateDiagonalTailChunk000Sub000Block062Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part023] using hcert

def TailChunk000Sub000Block062Part024SupportExplicit : Finset ℕ :=
  ([2638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block062Part024 : ℚ :=
  (108691568475 : ℚ) / 2515169426111896

def SurrogateDiagonalTailChunk000Sub000Block062Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2638
    = surrogateDiagTailX0RatChunk000Sub000Block062Part024

theorem surrogateDiagonalTailChunk000Sub000Block062Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block062Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block062Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block062Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block062Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block062Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block062HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block062Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block062Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block062Part000
    + surrogateDiagTailX0RatChunk000Sub000Block062Part001
    + surrogateDiagTailX0RatChunk000Sub000Block062Part002
    + surrogateDiagTailX0RatChunk000Sub000Block062Part003
    + surrogateDiagTailX0RatChunk000Sub000Block062Part004
    + surrogateDiagTailX0RatChunk000Sub000Block062Part005
    + surrogateDiagTailX0RatChunk000Sub000Block062Part006
    + surrogateDiagTailX0RatChunk000Sub000Block062Part007
    + surrogateDiagTailX0RatChunk000Sub000Block062Part008
    + surrogateDiagTailX0RatChunk000Sub000Block062Part009

def surrogateDiagonalTailChunk000Sub000Block062MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block062Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block062Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block062Part010
    + surrogateDiagTailX0RatChunk000Sub000Block062Part011
    + surrogateDiagTailX0RatChunk000Sub000Block062Part012
    + surrogateDiagTailX0RatChunk000Sub000Block062Part013
    + surrogateDiagTailX0RatChunk000Sub000Block062Part014
    + surrogateDiagTailX0RatChunk000Sub000Block062Part015
    + surrogateDiagTailX0RatChunk000Sub000Block062Part016
    + surrogateDiagTailX0RatChunk000Sub000Block062Part017
    + surrogateDiagTailX0RatChunk000Sub000Block062Part018
    + surrogateDiagTailX0RatChunk000Sub000Block062Part019

def surrogateDiagonalTailChunk000Sub000Block062TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block062Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block062Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block062Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block062Part020
    + surrogateDiagTailX0RatChunk000Sub000Block062Part021
    + surrogateDiagTailX0RatChunk000Sub000Block062Part022
    + surrogateDiagTailX0RatChunk000Sub000Block062Part023
    + surrogateDiagTailX0RatChunk000Sub000Block062Part024

def surrogateDiagonalTailChunk000Sub000Block062Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block062HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block062MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block062TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block062 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block062Part000
    + surrogateDiagTailX0RatChunk000Sub000Block062Part001
    + surrogateDiagTailX0RatChunk000Sub000Block062Part002
    + surrogateDiagTailX0RatChunk000Sub000Block062Part003
    + surrogateDiagTailX0RatChunk000Sub000Block062Part004
    + surrogateDiagTailX0RatChunk000Sub000Block062Part005
    + surrogateDiagTailX0RatChunk000Sub000Block062Part006
    + surrogateDiagTailX0RatChunk000Sub000Block062Part007
    + surrogateDiagTailX0RatChunk000Sub000Block062Part008
    + surrogateDiagTailX0RatChunk000Sub000Block062Part009
    + surrogateDiagTailX0RatChunk000Sub000Block062Part010
    + surrogateDiagTailX0RatChunk000Sub000Block062Part011
    + surrogateDiagTailX0RatChunk000Sub000Block062Part012
    + surrogateDiagTailX0RatChunk000Sub000Block062Part013
    + surrogateDiagTailX0RatChunk000Sub000Block062Part014
    + surrogateDiagTailX0RatChunk000Sub000Block062Part015
    + surrogateDiagTailX0RatChunk000Sub000Block062Part016
    + surrogateDiagTailX0RatChunk000Sub000Block062Part017
    + surrogateDiagTailX0RatChunk000Sub000Block062Part018
    + surrogateDiagTailX0RatChunk000Sub000Block062Part019
    + surrogateDiagTailX0RatChunk000Sub000Block062Part020
    + surrogateDiagTailX0RatChunk000Sub000Block062Part021
    + surrogateDiagTailX0RatChunk000Sub000Block062Part022
    + surrogateDiagTailX0RatChunk000Sub000Block062Part023
    + surrogateDiagTailX0RatChunk000Sub000Block062Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block062_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block062Head + surrogateDiagTailX0RatChunk000Sub000Block062Mid + surrogateDiagTailX0RatChunk000Sub000Block062Tail =
      surrogateDiagTailX0RatChunk000Sub000Block062 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block062Head surrogateDiagTailX0RatChunk000Sub000Block062Mid surrogateDiagTailX0RatChunk000Sub000Block062Tail surrogateDiagTailX0RatChunk000Sub000Block062
  ring

def SurrogateDiagonalTailChunk000Sub000Block062HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block062HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block062Head

def SurrogateDiagonalTailChunk000Sub000Block062MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block062MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block062Mid

def SurrogateDiagonalTailChunk000Sub000Block062TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block062TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block062Tail

theorem surrogateDiagonalTailChunk000Sub000Block062_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block062HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block062MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block062TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block062Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block062 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block062HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block062MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block062TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block062Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block062_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
