import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [14,15). -/

/- Block 014 covers tail-support indices [350,375) and q from 626 to 665. -/

def TailChunk000Sub000Block014Part000SupportExplicit : Finset ℕ :=
  ([626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part000 : ℚ :=
  (12209386625 : ℚ) / 2961796720896

def SurrogateDiagonalTailChunk000Sub000Block014Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 626
    = surrogateDiagTailX0RatChunk000Sub000Block014Part000

theorem surrogateDiagonalTailChunk000Sub000Block014Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part000] using hcert

def TailChunk000Sub000Block014Part001SupportExplicit : Finset ℕ :=
  ([627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part001 : ℚ :=
  (376181017 : ℚ) / 139995993600

def SurrogateDiagonalTailChunk000Sub000Block014Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 627
    = surrogateDiagTailX0RatChunk000Sub000Block014Part001

theorem surrogateDiagonalTailChunk000Sub000Block014Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part001] using hcert

def TailChunk000Sub000Block014Part002SupportExplicit : Finset ℕ :=
  ([629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part002 : ℚ :=
  (90536718725 : ℚ) / 137621661548544

def SurrogateDiagonalTailChunk000Sub000Block014Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 629
    = surrogateDiagTailX0RatChunk000Sub000Block014Part002

theorem surrogateDiagonalTailChunk000Sub000Block014Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part002] using hcert

def TailChunk000Sub000Block014Part003SupportExplicit : Finset ℕ :=
  ([631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part003 : ℚ :=
  (1988017873 : ℚ) / 3939027898050

def SurrogateDiagonalTailChunk000Sub000Block014Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 631
    = surrogateDiagTailX0RatChunk000Sub000Block014Part003

theorem surrogateDiagonalTailChunk000Sub000Block014Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part003] using hcert

def TailChunk000Sub000Block014Part004SupportExplicit : Finset ℕ :=
  ([633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part004 : ℚ :=
  (16879 : ℚ) / 9878400

def SurrogateDiagonalTailChunk000Sub000Block014Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 633
    = surrogateDiagTailX0RatChunk000Sub000Block014Part004

theorem surrogateDiagonalTailChunk000Sub000Block014Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part004] using hcert

def TailChunk000Sub000Block014Part005SupportExplicit : Finset ℕ :=
  ([634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part005 : ℚ :=
  (12523441625 : ℚ) / 3116629681296

def SurrogateDiagonalTailChunk000Sub000Block014Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 634
    = surrogateDiagTailX0RatChunk000Sub000Block014Part005

theorem surrogateDiagonalTailChunk000Sub000Block014Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part005] using hcert

def TailChunk000Sub000Block014Part006SupportExplicit : Finset ℕ :=
  ([635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part006 : ℚ :=
  (8835579175 : ℚ) / 8963476816896

def SurrogateDiagonalTailChunk000Sub000Block014Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 635
    = surrogateDiagTailX0RatChunk000Sub000Block014Part006

theorem surrogateDiagonalTailChunk000Sub000Block014Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part006] using hcert

def TailChunk000Sub000Block014Part007SupportExplicit : Finset ℕ :=
  ([638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part007 : ℚ :=
  (142527649 : ℚ) / 24591157248

def SurrogateDiagonalTailChunk000Sub000Block014Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 638
    = surrogateDiagTailX0RatChunk000Sub000Block014Part007

theorem surrogateDiagonalTailChunk000Sub000Block014Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part007] using hcert

def TailChunk000Sub000Block014Part008SupportExplicit : Finset ℕ :=
  ([641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part008 : ℚ :=
  (7181788999 : ℚ) / 16780571443200

def SurrogateDiagonalTailChunk000Sub000Block014Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 641
    = surrogateDiagTailX0RatChunk000Sub000Block014Part008

theorem surrogateDiagonalTailChunk000Sub000Block014Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part008] using hcert

def TailChunk000Sub000Block014Part009SupportExplicit : Finset ℕ :=
  ([642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part009 : ℚ :=
  (67346260975 : ℚ) / 5050917821568

def SurrogateDiagonalTailChunk000Sub000Block014Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 642
    = surrogateDiagTailX0RatChunk000Sub000Block014Part009

theorem surrogateDiagonalTailChunk000Sub000Block014Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part009] using hcert

def TailChunk000Sub000Block014Part010SupportExplicit : Finset ℕ :=
  ([643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part010 : ℚ :=
  (51608771425 : ℚ) / 106195711705362

def SurrogateDiagonalTailChunk000Sub000Block014Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 643
    = surrogateDiagTailX0RatChunk000Sub000Block014Part010

theorem surrogateDiagonalTailChunk000Sub000Block014Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part010] using hcert

def TailChunk000Sub000Block014Part011SupportExplicit : Finset ℕ :=
  ([645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part011 : ℚ :=
  (5612541475 : ℚ) / 1770563321856

def SurrogateDiagonalTailChunk000Sub000Block014Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 645
    = surrogateDiagTailX0RatChunk000Sub000Block014Part011

theorem surrogateDiagonalTailChunk000Sub000Block014Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part011] using hcert

def TailChunk000Sub000Block014Part012SupportExplicit : Finset ℕ :=
  ([646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part012 : ℚ :=
  (15448442675 : ℚ) / 2867117948928

def SurrogateDiagonalTailChunk000Sub000Block014Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 646
    = surrogateDiagTailX0RatChunk000Sub000Block014Part012

theorem surrogateDiagonalTailChunk000Sub000Block014Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part012] using hcert

def TailChunk000Sub000Block014Part013SupportExplicit : Finset ℕ :=
  ([647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part013 : ℚ :=
  (52252868425 : ℚ) / 108867171490482

def SurrogateDiagonalTailChunk000Sub000Block014Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 647
    = surrogateDiagTailX0RatChunk000Sub000Block014Part013

theorem surrogateDiagonalTailChunk000Sub000Block014Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part013] using hcert

def TailChunk000Sub000Block014Part014SupportExplicit : Finset ℕ :=
  ([649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part014 : ℚ :=
  (3749988617 : ℚ) / 5659379649600

def SurrogateDiagonalTailChunk000Sub000Block014Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 649
    = surrogateDiagTailX0RatChunk000Sub000Block014Part014

theorem surrogateDiagonalTailChunk000Sub000Block014Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part014] using hcert

def TailChunk000Sub000Block014Part015SupportExplicit : Finset ℕ :=
  ([651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part015 : ℚ :=
  (160659511 : ℚ) / 62220441600

def SurrogateDiagonalTailChunk000Sub000Block014Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 651
    = surrogateDiagTailX0RatChunk000Sub000Block014Part015

theorem surrogateDiagonalTailChunk000Sub000Block014Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part015] using hcert

def TailChunk000Sub000Block014Part016SupportExplicit : Finset ℕ :=
  ([653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part016 : ℚ :=
  (53226503425 : ℚ) / 112968470936352

def SurrogateDiagonalTailChunk000Sub000Block014Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 653
    = surrogateDiagTailX0RatChunk000Sub000Block014Part016

theorem surrogateDiagonalTailChunk000Sub000Block014Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part016] using hcert

def TailChunk000Sub000Block014Part017SupportExplicit : Finset ℕ :=
  ([654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part017 : ℚ :=
  (66971680675 : ℚ) / 5443044231168

def SurrogateDiagonalTailChunk000Sub000Block014Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 654
    = surrogateDiagTailX0RatChunk000Sub000Block014Part017

theorem surrogateDiagonalTailChunk000Sub000Block014Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part017] using hcert

def TailChunk000Sub000Block014Part018SupportExplicit : Finset ℕ :=
  ([655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part018 : ℚ :=
  (3046285991 : ℚ) / 3656539161600

def SurrogateDiagonalTailChunk000Sub000Block014Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 655
    = surrogateDiagTailX0RatChunk000Sub000Block014Part018

theorem surrogateDiagonalTailChunk000Sub000Block014Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part018] using hcert

def TailChunk000Sub000Block014Part019SupportExplicit : Finset ℕ :=
  ([658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part019 : ℚ :=
  (42650891375 : ℚ) / 7254929415744

def SurrogateDiagonalTailChunk000Sub000Block014Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 658
    = surrogateDiagTailX0RatChunk000Sub000Block014Part019

theorem surrogateDiagonalTailChunk000Sub000Block014Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part019] using hcert

def TailChunk000Sub000Block014Part020SupportExplicit : Finset ℕ :=
  ([659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part020 : ℚ :=
  (54209125825 : ℚ) / 117184573038162

def SurrogateDiagonalTailChunk000Sub000Block014Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 659
    = surrogateDiagTailX0RatChunk000Sub000Block014Part020

theorem surrogateDiagonalTailChunk000Sub000Block014Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part020] using hcert

def TailChunk000Sub000Block014Part021SupportExplicit : Finset ℕ :=
  ([661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part021 : ℚ :=
  (694267469 : ℚ) / 1725320995200

def SurrogateDiagonalTailChunk000Sub000Block014Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 661
    = surrogateDiagTailX0RatChunk000Sub000Block014Part021

theorem surrogateDiagonalTailChunk000Sub000Block014Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part021] using hcert

def TailChunk000Sub000Block014Part022SupportExplicit : Finset ℕ :=
  ([662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part022 : ℚ :=
  (30348397 : ℚ) / 8786356920

def SurrogateDiagonalTailChunk000Sub000Block014Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 662
    = surrogateDiagTailX0RatChunk000Sub000Block014Part022

theorem surrogateDiagonalTailChunk000Sub000Block014Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part022] using hcert

def TailChunk000Sub000Block014Part023SupportExplicit : Finset ℕ :=
  ([663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part023 : ℚ :=
  (2441024825 : ℚ) / 1132688572416

def SurrogateDiagonalTailChunk000Sub000Block014Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 663
    = surrogateDiagTailX0RatChunk000Sub000Block014Part023

theorem surrogateDiagonalTailChunk000Sub000Block014Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part023] using hcert

def TailChunk000Sub000Block014Part024SupportExplicit : Finset ℕ :=
  ([665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block014Part024 : ℚ :=
  (46505423525 : ℚ) / 29029569232896

def SurrogateDiagonalTailChunk000Sub000Block014Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 665
    = surrogateDiagTailX0RatChunk000Sub000Block014Part024

theorem surrogateDiagonalTailChunk000Sub000Block014Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block014Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block014Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block014Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block014Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block014Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block014HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block014Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block014Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block014Part000
    + surrogateDiagTailX0RatChunk000Sub000Block014Part001
    + surrogateDiagTailX0RatChunk000Sub000Block014Part002
    + surrogateDiagTailX0RatChunk000Sub000Block014Part003
    + surrogateDiagTailX0RatChunk000Sub000Block014Part004
    + surrogateDiagTailX0RatChunk000Sub000Block014Part005
    + surrogateDiagTailX0RatChunk000Sub000Block014Part006
    + surrogateDiagTailX0RatChunk000Sub000Block014Part007
    + surrogateDiagTailX0RatChunk000Sub000Block014Part008
    + surrogateDiagTailX0RatChunk000Sub000Block014Part009

def surrogateDiagonalTailChunk000Sub000Block014MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block014Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block014Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block014Part010
    + surrogateDiagTailX0RatChunk000Sub000Block014Part011
    + surrogateDiagTailX0RatChunk000Sub000Block014Part012
    + surrogateDiagTailX0RatChunk000Sub000Block014Part013
    + surrogateDiagTailX0RatChunk000Sub000Block014Part014
    + surrogateDiagTailX0RatChunk000Sub000Block014Part015
    + surrogateDiagTailX0RatChunk000Sub000Block014Part016
    + surrogateDiagTailX0RatChunk000Sub000Block014Part017
    + surrogateDiagTailX0RatChunk000Sub000Block014Part018
    + surrogateDiagTailX0RatChunk000Sub000Block014Part019

def surrogateDiagonalTailChunk000Sub000Block014TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block014Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block014Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block014Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block014Part020
    + surrogateDiagTailX0RatChunk000Sub000Block014Part021
    + surrogateDiagTailX0RatChunk000Sub000Block014Part022
    + surrogateDiagTailX0RatChunk000Sub000Block014Part023
    + surrogateDiagTailX0RatChunk000Sub000Block014Part024

def surrogateDiagonalTailChunk000Sub000Block014Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block014HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block014MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block014TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block014 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block014Part000
    + surrogateDiagTailX0RatChunk000Sub000Block014Part001
    + surrogateDiagTailX0RatChunk000Sub000Block014Part002
    + surrogateDiagTailX0RatChunk000Sub000Block014Part003
    + surrogateDiagTailX0RatChunk000Sub000Block014Part004
    + surrogateDiagTailX0RatChunk000Sub000Block014Part005
    + surrogateDiagTailX0RatChunk000Sub000Block014Part006
    + surrogateDiagTailX0RatChunk000Sub000Block014Part007
    + surrogateDiagTailX0RatChunk000Sub000Block014Part008
    + surrogateDiagTailX0RatChunk000Sub000Block014Part009
    + surrogateDiagTailX0RatChunk000Sub000Block014Part010
    + surrogateDiagTailX0RatChunk000Sub000Block014Part011
    + surrogateDiagTailX0RatChunk000Sub000Block014Part012
    + surrogateDiagTailX0RatChunk000Sub000Block014Part013
    + surrogateDiagTailX0RatChunk000Sub000Block014Part014
    + surrogateDiagTailX0RatChunk000Sub000Block014Part015
    + surrogateDiagTailX0RatChunk000Sub000Block014Part016
    + surrogateDiagTailX0RatChunk000Sub000Block014Part017
    + surrogateDiagTailX0RatChunk000Sub000Block014Part018
    + surrogateDiagTailX0RatChunk000Sub000Block014Part019
    + surrogateDiagTailX0RatChunk000Sub000Block014Part020
    + surrogateDiagTailX0RatChunk000Sub000Block014Part021
    + surrogateDiagTailX0RatChunk000Sub000Block014Part022
    + surrogateDiagTailX0RatChunk000Sub000Block014Part023
    + surrogateDiagTailX0RatChunk000Sub000Block014Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block014_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block014Head + surrogateDiagTailX0RatChunk000Sub000Block014Mid + surrogateDiagTailX0RatChunk000Sub000Block014Tail =
      surrogateDiagTailX0RatChunk000Sub000Block014 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block014Head surrogateDiagTailX0RatChunk000Sub000Block014Mid surrogateDiagTailX0RatChunk000Sub000Block014Tail surrogateDiagTailX0RatChunk000Sub000Block014
  ring

def SurrogateDiagonalTailChunk000Sub000Block014HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block014HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block014Head

def SurrogateDiagonalTailChunk000Sub000Block014MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block014MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block014Mid

def SurrogateDiagonalTailChunk000Sub000Block014TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block014TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block014Tail

theorem surrogateDiagonalTailChunk000Sub000Block014_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block014HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block014MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block014TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block014Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block014 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block014HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block014MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block014TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block014Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block014_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
