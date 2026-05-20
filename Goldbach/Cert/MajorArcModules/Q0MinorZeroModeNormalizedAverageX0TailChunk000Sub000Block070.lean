import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [70,71). -/

/- Block 070 covers tail-support indices [1750,1775) and q from 2931 to 2969. -/

def TailChunk000Sub000Block070Part000SupportExplicit : Finset ℕ :=
  ([2931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part000 : ℚ :=
  (655639609975 : ℚ) / 36303300639326208

def SurrogateDiagonalTailChunk000Sub000Block070Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2931
    = surrogateDiagTailX0RatChunk000Sub000Block070Part000

theorem surrogateDiagonalTailChunk000Sub000Block070Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part000] using hcert

def TailChunk000Sub000Block070Part001SupportExplicit : Finset ℕ :=
  ([2933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part001 : ℚ :=
  (448750218725 : ℚ) / 49466022631401024

def SurrogateDiagonalTailChunk000Sub000Block070Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2933
    = surrogateDiagTailX0RatChunk000Sub000Block070Part001

theorem surrogateDiagonalTailChunk000Sub000Block070Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part001] using hcert

def TailChunk000Sub000Block070Part002SupportExplicit : Finset ℕ :=
  ([2935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part002 : ℚ :=
  (419219859575 : ℚ) / 37742207033140224

def SurrogateDiagonalTailChunk000Sub000Block070Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2935
    = surrogateDiagTailX0RatChunk000Sub000Block070Part002

theorem surrogateDiagonalTailChunk000Sub000Block070Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part002] using hcert

def TailChunk000Sub000Block070Part003SupportExplicit : Finset ℕ :=
  ([2937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part003 : ℚ :=
  (8894995847 : ℚ) / 479852239257600

def SurrogateDiagonalTailChunk000Sub000Block070Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2937
    = surrogateDiagTailX0RatChunk000Sub000Block070Part003

theorem surrogateDiagonalTailChunk000Sub000Block070Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part003] using hcert

def TailChunk000Sub000Block070Part004SupportExplicit : Finset ℕ :=
  ([2938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part004 : ℚ :=
  (375409128925 : ℚ) / 8158755787112448

def SurrogateDiagonalTailChunk000Sub000Block070Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2938
    = surrogateDiagTailX0RatChunk000Sub000Block070Part004

theorem surrogateDiagonalTailChunk000Sub000Block070Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part004] using hcert

def TailChunk000Sub000Block070Part005SupportExplicit : Finset ℕ :=
  ([2939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part005 : ℚ :=
  (134964390625 : ℚ) / 46577270366565042

def SurrogateDiagonalTailChunk000Sub000Block070Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2939
    = surrogateDiagTailX0RatChunk000Sub000Block070Part005

theorem surrogateDiagonalTailChunk000Sub000Block070Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part005] using hcert

def TailChunk000Sub000Block070Part006SupportExplicit : Finset ℕ :=
  ([2941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part006 : ℚ :=
  (176716246725 : ℚ) / 47807862025486336

def SurrogateDiagonalTailChunk000Sub000Block070Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2941
    = surrogateDiagTailX0RatChunk000Sub000Block070Part006

theorem surrogateDiagonalTailChunk000Sub000Block070Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part006] using hcert

def TailChunk000Sub000Block070Part007SupportExplicit : Finset ℕ :=
  ([2942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part007 : ℚ :=
  (10812713477 : ℚ) / 233521135388100

def SurrogateDiagonalTailChunk000Sub000Block070Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2942
    = surrogateDiagTailX0RatChunk000Sub000Block070Part007

theorem surrogateDiagonalTailChunk000Sub000Block070Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part007] using hcert

def TailChunk000Sub000Block070Part008SupportExplicit : Finset ℕ :=
  ([2945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part008 : ℚ :=
  (15342188669 : ℚ) / 1088608846233600

def SurrogateDiagonalTailChunk000Sub000Block070Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2945
    = surrogateDiagTailX0RatChunk000Sub000Block070Part008

theorem surrogateDiagonalTailChunk000Sub000Block070Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part008] using hcert

def TailChunk000Sub000Block070Part009SupportExplicit : Finset ℕ :=
  ([2946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part009 : ℚ :=
  (11431872901 : ℚ) / 92255263363200

def SurrogateDiagonalTailChunk000Sub000Block070Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2946
    = surrogateDiagTailX0RatChunk000Sub000Block070Part009

theorem surrogateDiagonalTailChunk000Sub000Block070Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part009] using hcert

def TailChunk000Sub000Block070Part010SupportExplicit : Finset ℕ :=
  ([2947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part010 : ℚ :=
  (18121831421 : ℚ) / 2016782283801600

def SurrogateDiagonalTailChunk000Sub000Block070Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2947
    = surrogateDiagTailX0RatChunk000Sub000Block070Part010

theorem surrogateDiagonalTailChunk000Sub000Block070Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part010] using hcert

def TailChunk000Sub000Block070Part011SupportExplicit : Finset ℕ :=
  ([2949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part011 : ℚ :=
  (663717828325 : ℚ) / 37204270445255808

def SurrogateDiagonalTailChunk000Sub000Block070Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2949
    = surrogateDiagTailX0RatChunk000Sub000Block070Part011

theorem surrogateDiagonalTailChunk000Sub000Block070Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part011] using hcert

def TailChunk000Sub000Block070Part012SupportExplicit : Finset ℕ :=
  ([2951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part012 : ℚ :=
  (493567212125 : ℚ) / 67632525354230784

def SurrogateDiagonalTailChunk000Sub000Block070Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2951
    = surrogateDiagTailX0RatChunk000Sub000Block070Part012

theorem surrogateDiagonalTailChunk000Sub000Block070Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part012] using hcert

def TailChunk000Sub000Block070Part013SupportExplicit : Finset ℕ :=
  ([2953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part013 : ℚ :=
  (1089808119775 : ℚ) / 189885705058142208

def SurrogateDiagonalTailChunk000Sub000Block070Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2953
    = surrogateDiagTailX0RatChunk000Sub000Block070Part013

theorem surrogateDiagonalTailChunk000Sub000Block070Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part013] using hcert

def TailChunk000Sub000Block070Part014SupportExplicit : Finset ℕ :=
  ([2954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part014 : ℚ :=
  (25219693 : ℚ) / 444616905600

def SurrogateDiagonalTailChunk000Sub000Block070Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2954
    = surrogateDiagTailX0RatChunk000Sub000Block070Part014

theorem surrogateDiagonalTailChunk000Sub000Block070Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part014] using hcert

def TailChunk000Sub000Block070Part015SupportExplicit : Finset ℕ :=
  ([2955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part015 : ℚ :=
  (102075340525 : ℚ) / 3778775587356672

def SurrogateDiagonalTailChunk000Sub000Block070Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2955
    = surrogateDiagTailX0RatChunk000Sub000Block070Part015

theorem surrogateDiagonalTailChunk000Sub000Block070Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part015] using hcert

def TailChunk000Sub000Block070Part016SupportExplicit : Finset ℕ :=
  ([2957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part016 : ℚ :=
  (136622640625 : ℚ) / 47729247403252512

def SurrogateDiagonalTailChunk000Sub000Block070Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2957
    = surrogateDiagTailX0RatChunk000Sub000Block070Part016

theorem surrogateDiagonalTailChunk000Sub000Block070Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part016] using hcert

def TailChunk000Sub000Block070Part017SupportExplicit : Finset ℕ :=
  ([2958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part017 : ℚ :=
  (263934210625 : ℚ) / 1611606081404928

def SurrogateDiagonalTailChunk000Sub000Block070Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2958
    = surrogateDiagTailX0RatChunk000Sub000Block070Part017

theorem surrogateDiagonalTailChunk000Sub000Block070Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part017] using hcert

def TailChunk000Sub000Block070Part018SupportExplicit : Finset ℕ :=
  ([2959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part018 : ℚ :=
  (19548293957 : ℚ) / 2579859356697600

def SurrogateDiagonalTailChunk000Sub000Block070Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2959
    = surrogateDiagTailX0RatChunk000Sub000Block070Part018

theorem surrogateDiagonalTailChunk000Sub000Block070Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part018] using hcert

def TailChunk000Sub000Block070Part019SupportExplicit : Finset ℕ :=
  ([2962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part019 : ℚ :=
  (5481209139 : ℚ) / 159960391014400

def SurrogateDiagonalTailChunk000Sub000Block070Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2962
    = surrogateDiagTailX0RatChunk000Sub000Block070Part019

theorem surrogateDiagonalTailChunk000Sub000Block070Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part019] using hcert

def TailChunk000Sub000Block070Part020SupportExplicit : Finset ℕ :=
  ([2963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part020 : ℚ :=
  (1097201640775 : ℚ) / 192471785712650568

def SurrogateDiagonalTailChunk000Sub000Block070Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2963
    = surrogateDiagTailX0RatChunk000Sub000Block070Part020

theorem surrogateDiagonalTailChunk000Sub000Block070Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part020] using hcert

def TailChunk000Sub000Block070Part021SupportExplicit : Finset ℕ :=
  ([2965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part021 : ℚ :=
  (277916627025 : ℚ) / 26207910463799296

def SurrogateDiagonalTailChunk000Sub000Block070Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2965
    = surrogateDiagTailX0RatChunk000Sub000Block070Part021

theorem surrogateDiagonalTailChunk000Sub000Block070Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part021] using hcert

def TailChunk000Sub000Block070Part022SupportExplicit : Finset ℕ :=
  ([2966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part022 : ℚ :=
  (45800193425 : ℚ) / 1340223300221832

def SurrogateDiagonalTailChunk000Sub000Block070Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2966
    = surrogateDiagTailX0RatChunk000Sub000Block070Part022

theorem surrogateDiagonalTailChunk000Sub000Block070Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part022] using hcert

def TailChunk000Sub000Block070Part023SupportExplicit : Finset ℕ :=
  ([2967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part023 : ℚ :=
  (89288364925 : ℚ) / 4166167113529344

def SurrogateDiagonalTailChunk000Sub000Block070Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2967
    = surrogateDiagTailX0RatChunk000Sub000Block070Part023

theorem surrogateDiagonalTailChunk000Sub000Block070Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part023] using hcert

def TailChunk000Sub000Block070Part024SupportExplicit : Finset ℕ :=
  ([2969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block070Part024 : ℚ :=
  (1101649750975 : ℚ) / 194036059033356288

def SurrogateDiagonalTailChunk000Sub000Block070Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2969
    = surrogateDiagTailX0RatChunk000Sub000Block070Part024

theorem surrogateDiagonalTailChunk000Sub000Block070Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block070Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block070Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block070Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block070Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block070Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block070HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block070Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block070Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block070Part000
    + surrogateDiagTailX0RatChunk000Sub000Block070Part001
    + surrogateDiagTailX0RatChunk000Sub000Block070Part002
    + surrogateDiagTailX0RatChunk000Sub000Block070Part003
    + surrogateDiagTailX0RatChunk000Sub000Block070Part004
    + surrogateDiagTailX0RatChunk000Sub000Block070Part005
    + surrogateDiagTailX0RatChunk000Sub000Block070Part006
    + surrogateDiagTailX0RatChunk000Sub000Block070Part007
    + surrogateDiagTailX0RatChunk000Sub000Block070Part008
    + surrogateDiagTailX0RatChunk000Sub000Block070Part009

def surrogateDiagonalTailChunk000Sub000Block070MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block070Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block070Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block070Part010
    + surrogateDiagTailX0RatChunk000Sub000Block070Part011
    + surrogateDiagTailX0RatChunk000Sub000Block070Part012
    + surrogateDiagTailX0RatChunk000Sub000Block070Part013
    + surrogateDiagTailX0RatChunk000Sub000Block070Part014
    + surrogateDiagTailX0RatChunk000Sub000Block070Part015
    + surrogateDiagTailX0RatChunk000Sub000Block070Part016
    + surrogateDiagTailX0RatChunk000Sub000Block070Part017
    + surrogateDiagTailX0RatChunk000Sub000Block070Part018
    + surrogateDiagTailX0RatChunk000Sub000Block070Part019

def surrogateDiagonalTailChunk000Sub000Block070TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block070Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block070Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block070Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block070Part020
    + surrogateDiagTailX0RatChunk000Sub000Block070Part021
    + surrogateDiagTailX0RatChunk000Sub000Block070Part022
    + surrogateDiagTailX0RatChunk000Sub000Block070Part023
    + surrogateDiagTailX0RatChunk000Sub000Block070Part024

def surrogateDiagonalTailChunk000Sub000Block070Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block070HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block070MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block070TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block070 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block070Part000
    + surrogateDiagTailX0RatChunk000Sub000Block070Part001
    + surrogateDiagTailX0RatChunk000Sub000Block070Part002
    + surrogateDiagTailX0RatChunk000Sub000Block070Part003
    + surrogateDiagTailX0RatChunk000Sub000Block070Part004
    + surrogateDiagTailX0RatChunk000Sub000Block070Part005
    + surrogateDiagTailX0RatChunk000Sub000Block070Part006
    + surrogateDiagTailX0RatChunk000Sub000Block070Part007
    + surrogateDiagTailX0RatChunk000Sub000Block070Part008
    + surrogateDiagTailX0RatChunk000Sub000Block070Part009
    + surrogateDiagTailX0RatChunk000Sub000Block070Part010
    + surrogateDiagTailX0RatChunk000Sub000Block070Part011
    + surrogateDiagTailX0RatChunk000Sub000Block070Part012
    + surrogateDiagTailX0RatChunk000Sub000Block070Part013
    + surrogateDiagTailX0RatChunk000Sub000Block070Part014
    + surrogateDiagTailX0RatChunk000Sub000Block070Part015
    + surrogateDiagTailX0RatChunk000Sub000Block070Part016
    + surrogateDiagTailX0RatChunk000Sub000Block070Part017
    + surrogateDiagTailX0RatChunk000Sub000Block070Part018
    + surrogateDiagTailX0RatChunk000Sub000Block070Part019
    + surrogateDiagTailX0RatChunk000Sub000Block070Part020
    + surrogateDiagTailX0RatChunk000Sub000Block070Part021
    + surrogateDiagTailX0RatChunk000Sub000Block070Part022
    + surrogateDiagTailX0RatChunk000Sub000Block070Part023
    + surrogateDiagTailX0RatChunk000Sub000Block070Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block070_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block070Head + surrogateDiagTailX0RatChunk000Sub000Block070Mid + surrogateDiagTailX0RatChunk000Sub000Block070Tail =
      surrogateDiagTailX0RatChunk000Sub000Block070 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block070Head surrogateDiagTailX0RatChunk000Sub000Block070Mid surrogateDiagTailX0RatChunk000Sub000Block070Tail surrogateDiagTailX0RatChunk000Sub000Block070
  ring

def SurrogateDiagonalTailChunk000Sub000Block070HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block070HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block070Head

def SurrogateDiagonalTailChunk000Sub000Block070MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block070MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block070Mid

def SurrogateDiagonalTailChunk000Sub000Block070TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block070TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block070Tail

theorem surrogateDiagonalTailChunk000Sub000Block070_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block070HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block070MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block070TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block070Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block070 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block070HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block070MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block070TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block070Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block070_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
