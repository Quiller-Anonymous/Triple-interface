import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [171,172). -/

/-- Block 171 covers tail-support indices [4275,4300) and q from 7086 to 7126. -/

def TailChunk000Sub000Block171Part000SupportExplicit : Finset ℕ :=
  ([7086] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part000 : ℚ :=
  (24396168517 : ℚ) / 3102664824883200

def SurrogateDiagonalTailChunk000Sub000Block171Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7086
    = surrogateDiagTailX0RatChunk000Sub000Block171Part000

theorem surrogateDiagonalTailChunk000Sub000Block171Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part000] using hcert

def TailChunk000Sub000Block171Part001SupportExplicit : Finset ℕ :=
  ([7087] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part001 : ℚ :=
  (2912184375925 : ℚ) / 5026765651412502528

def SurrogateDiagonalTailChunk000Sub000Block171Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7087
    = surrogateDiagTailX0RatChunk000Sub000Block171Part001

theorem surrogateDiagonalTailChunk000Sub000Block171Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part001] using hcert

def TailChunk000Sub000Block171Part002SupportExplicit : Finset ℕ :=
  ([7089] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part002 : ℚ :=
  (1613431776175 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub000Block171Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7089
    = surrogateDiagTailX0RatChunk000Sub000Block171Part002

theorem surrogateDiagonalTailChunk000Sub000Block171Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part002] using hcert

def TailChunk000Sub000Block171Part003SupportExplicit : Finset ℕ :=
  ([7090] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part003 : ℚ :=
  (230200148825 : ℚ) / 53614048173981696

def SurrogateDiagonalTailChunk000Sub000Block171Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7090
    = surrogateDiagTailX0RatChunk000Sub000Block171Part003

theorem surrogateDiagonalTailChunk000Sub000Block171Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part003] using hcert

def TailChunk000Sub000Block171Part004SupportExplicit : Finset ℕ :=
  ([7091] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part004 : ℚ :=
  (2562692923375 : ℚ) / 3399021490429052928

def SurrogateDiagonalTailChunk000Sub000Block171Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7091
    = surrogateDiagTailX0RatChunk000Sub000Block171Part004

theorem surrogateDiagonalTailChunk000Sub000Block171Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part004] using hcert

def TailChunk000Sub000Block171Part005SupportExplicit : Finset ℕ :=
  ([7093] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part005 : ℚ :=
  (2812210123 : ℚ) / 5211612866150400

def SurrogateDiagonalTailChunk000Sub000Block171Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7093
    = surrogateDiagTailX0RatChunk000Sub000Block171Part005

theorem surrogateDiagonalTailChunk000Sub000Block171Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part005] using hcert

def TailChunk000Sub000Block171Part006SupportExplicit : Finset ℕ :=
  ([7094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part006 : ℚ :=
  (1572336594775 : ℚ) / 395350037150230728

def SurrogateDiagonalTailChunk000Sub000Block171Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7094
    = surrogateDiagTailX0RatChunk000Sub000Block171Part006

theorem surrogateDiagonalTailChunk000Sub000Block171Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part006] using hcert

def TailChunk000Sub000Block171Part007SupportExplicit : Finset ℕ :=
  ([7095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part007 : ℚ :=
  (51064007 : ℚ) / 14164506574848

def SurrogateDiagonalTailChunk000Sub000Block171Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7095
    = surrogateDiagTailX0RatChunk000Sub000Block171Part007

theorem surrogateDiagonalTailChunk000Sub000Block171Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part007] using hcert

def TailChunk000Sub000Block171Part008SupportExplicit : Finset ℕ :=
  ([7097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part008 : ℚ :=
  (1498945817 : ℚ) / 2798969682000000

def SurrogateDiagonalTailChunk000Sub000Block171Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7097
    = surrogateDiagTailX0RatChunk000Sub000Block171Part008

theorem surrogateDiagonalTailChunk000Sub000Block171Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part008] using hcert

def TailChunk000Sub000Block171Part009SupportExplicit : Finset ℕ :=
  ([7099] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part009 : ℚ :=
  (120087076021 : ℚ) / 218933014583347200

def SurrogateDiagonalTailChunk000Sub000Block171Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7099
    = surrogateDiagTailX0RatChunk000Sub000Block171Part009

theorem surrogateDiagonalTailChunk000Sub000Block171Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part009] using hcert

def TailChunk000Sub000Block171Part010SupportExplicit : Finset ℕ :=
  ([7102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part010 : ℚ :=
  (83803932425 : ℚ) / 19272740351394816

def SurrogateDiagonalTailChunk000Sub000Block171Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7102
    = surrogateDiagTailX0RatChunk000Sub000Block171Part010

theorem surrogateDiagonalTailChunk000Sub000Block171Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part010] using hcert

def TailChunk000Sub000Block171Part011SupportExplicit : Finset ℕ :=
  ([7103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part011 : ℚ :=
  (788322015625 : ℚ) / 1590338377866768402

def SurrogateDiagonalTailChunk000Sub000Block171Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7103
    = surrogateDiagTailX0RatChunk000Sub000Block171Part011

theorem surrogateDiagonalTailChunk000Sub000Block171Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part011] using hcert

def TailChunk000Sub000Block171Part012SupportExplicit : Finset ℕ :=
  ([7106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part012 : ℚ :=
  (16073578459 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block171Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7106
    = surrogateDiagTailX0RatChunk000Sub000Block171Part012

theorem surrogateDiagonalTailChunk000Sub000Block171Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part012] using hcert

def TailChunk000Sub000Block171Part013SupportExplicit : Finset ℕ :=
  ([7107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part013 : ℚ :=
  (1646574867625 : ℚ) / 1014467765274298368

def SurrogateDiagonalTailChunk000Sub000Block171Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7107
    = surrogateDiagTailX0RatChunk000Sub000Block171Part013

theorem surrogateDiagonalTailChunk000Sub000Block171Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part013] using hcert

def TailChunk000Sub000Block171Part014SupportExplicit : Finset ℕ :=
  ([7109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part014 : ℚ :=
  (789654390625 : ℚ) / 1595719470068558112

def SurrogateDiagonalTailChunk000Sub000Block171Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7109
    = surrogateDiagTailX0RatChunk000Sub000Block171Part014

theorem surrogateDiagonalTailChunk000Sub000Block171Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part014] using hcert

def TailChunk000Sub000Block171Part015SupportExplicit : Finset ℕ :=
  ([7111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part015 : ℚ :=
  (1515146125 : ℚ) / 2461594820840064

def SurrogateDiagonalTailChunk000Sub000Block171Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7111
    = surrogateDiagTailX0RatChunk000Sub000Block171Part015

theorem surrogateDiagonalTailChunk000Sub000Block171Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part015] using hcert

def TailChunk000Sub000Block171Part016SupportExplicit : Finset ℕ :=
  ([7113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part016 : ℚ :=
  (14051939309 : ℚ) / 25244700418497600

def SurrogateDiagonalTailChunk000Sub000Block171Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7113
    = surrogateDiagTailX0RatChunk000Sub000Block171Part016

theorem surrogateDiagonalTailChunk000Sub000Block171Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part016] using hcert

def TailChunk000Sub000Block171Part017SupportExplicit : Finset ℕ :=
  ([7114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part017 : ℚ :=
  (197691390625 : ℚ) / 99957152719617312

def SurrogateDiagonalTailChunk000Sub000Block171Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7114
    = surrogateDiagTailX0RatChunk000Sub000Block171Part017

theorem surrogateDiagonalTailChunk000Sub000Block171Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part017] using hcert

def TailChunk000Sub000Block171Part018SupportExplicit : Finset ℕ :=
  ([7115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part018 : ℚ :=
  (23764963075 : ℚ) / 163585658711864448

def SurrogateDiagonalTailChunk000Sub000Block171Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7115
    = surrogateDiagTailX0RatChunk000Sub000Block171Part018

theorem surrogateDiagonalTailChunk000Sub000Block171Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part018] using hcert

def TailChunk000Sub000Block171Part019SupportExplicit : Finset ℕ :=
  ([7117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part019 : ℚ :=
  (8459693083 : ℚ) / 174187474384771200

def SurrogateDiagonalTailChunk000Sub000Block171Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7117
    = surrogateDiagTailX0RatChunk000Sub000Block171Part019

theorem surrogateDiagonalTailChunk000Sub000Block171Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part019] using hcert

def TailChunk000Sub000Block171Part020SupportExplicit : Finset ℕ :=
  ([7118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part020 : ℚ :=
  (197913765625 : ℚ) / 100182217989920562

def SurrogateDiagonalTailChunk000Sub000Block171Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7118
    = surrogateDiagTailX0RatChunk000Sub000Block171Part020

theorem surrogateDiagonalTailChunk000Sub000Block171Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part020] using hcert

def TailChunk000Sub000Block171Part021SupportExplicit : Finset ℕ :=
  ([7121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block171Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7121
    = surrogateDiagTailX0RatChunk000Sub000Block171Part021

theorem surrogateDiagonalTailChunk000Sub000Block171Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part021] using hcert

def TailChunk000Sub000Block171Part022SupportExplicit : Finset ℕ :=
  ([7122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part022 : ℚ :=
  (616116027475 : ℚ) / 79156320387097728

def SurrogateDiagonalTailChunk000Sub000Block171Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7122
    = surrogateDiagTailX0RatChunk000Sub000Block171Part022

theorem surrogateDiagonalTailChunk000Sub000Block171Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part022] using hcert

def TailChunk000Sub000Block171Part023SupportExplicit : Finset ℕ :=
  ([7123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part023 : ℚ :=
  (45250670925 : ℚ) / 1667595297927725056

def SurrogateDiagonalTailChunk000Sub000Block171Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7123
    = surrogateDiagTailX0RatChunk000Sub000Block171Part023

theorem surrogateDiagonalTailChunk000Sub000Block171Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part023] using hcert

def TailChunk000Sub000Block171Part024SupportExplicit : Finset ℕ :=
  ([7126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block171Part024 : ℚ :=
  (80865903125 : ℚ) / 23979725100582912

def SurrogateDiagonalTailChunk000Sub000Block171Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7126
    = surrogateDiagTailX0RatChunk000Sub000Block171Part024

theorem surrogateDiagonalTailChunk000Sub000Block171Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block171Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block171Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block171Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block171Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block171Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block171HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block171Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block171Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part000
    + surrogateDiagTailX0RatChunk000Sub000Block171Part001
    + surrogateDiagTailX0RatChunk000Sub000Block171Part002
    + surrogateDiagTailX0RatChunk000Sub000Block171Part003
    + surrogateDiagTailX0RatChunk000Sub000Block171Part004
    + surrogateDiagTailX0RatChunk000Sub000Block171Part005
    + surrogateDiagTailX0RatChunk000Sub000Block171Part006
    + surrogateDiagTailX0RatChunk000Sub000Block171Part007
    + surrogateDiagTailX0RatChunk000Sub000Block171Part008
    + surrogateDiagTailX0RatChunk000Sub000Block171Part009

def surrogateDiagonalTailChunk000Sub000Block171MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block171Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block171Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part010
    + surrogateDiagTailX0RatChunk000Sub000Block171Part011
    + surrogateDiagTailX0RatChunk000Sub000Block171Part012
    + surrogateDiagTailX0RatChunk000Sub000Block171Part013
    + surrogateDiagTailX0RatChunk000Sub000Block171Part014
    + surrogateDiagTailX0RatChunk000Sub000Block171Part015
    + surrogateDiagTailX0RatChunk000Sub000Block171Part016
    + surrogateDiagTailX0RatChunk000Sub000Block171Part017
    + surrogateDiagTailX0RatChunk000Sub000Block171Part018
    + surrogateDiagTailX0RatChunk000Sub000Block171Part019

def surrogateDiagonalTailChunk000Sub000Block171TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block171Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block171Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block171Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part020
    + surrogateDiagTailX0RatChunk000Sub000Block171Part021
    + surrogateDiagTailX0RatChunk000Sub000Block171Part022
    + surrogateDiagTailX0RatChunk000Sub000Block171Part023
    + surrogateDiagTailX0RatChunk000Sub000Block171Part024

def surrogateDiagonalTailChunk000Sub000Block171Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block171HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block171MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block171TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block171 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block171Part000
    + surrogateDiagTailX0RatChunk000Sub000Block171Part001
    + surrogateDiagTailX0RatChunk000Sub000Block171Part002
    + surrogateDiagTailX0RatChunk000Sub000Block171Part003
    + surrogateDiagTailX0RatChunk000Sub000Block171Part004
    + surrogateDiagTailX0RatChunk000Sub000Block171Part005
    + surrogateDiagTailX0RatChunk000Sub000Block171Part006
    + surrogateDiagTailX0RatChunk000Sub000Block171Part007
    + surrogateDiagTailX0RatChunk000Sub000Block171Part008
    + surrogateDiagTailX0RatChunk000Sub000Block171Part009
    + surrogateDiagTailX0RatChunk000Sub000Block171Part010
    + surrogateDiagTailX0RatChunk000Sub000Block171Part011
    + surrogateDiagTailX0RatChunk000Sub000Block171Part012
    + surrogateDiagTailX0RatChunk000Sub000Block171Part013
    + surrogateDiagTailX0RatChunk000Sub000Block171Part014
    + surrogateDiagTailX0RatChunk000Sub000Block171Part015
    + surrogateDiagTailX0RatChunk000Sub000Block171Part016
    + surrogateDiagTailX0RatChunk000Sub000Block171Part017
    + surrogateDiagTailX0RatChunk000Sub000Block171Part018
    + surrogateDiagTailX0RatChunk000Sub000Block171Part019
    + surrogateDiagTailX0RatChunk000Sub000Block171Part020
    + surrogateDiagTailX0RatChunk000Sub000Block171Part021
    + surrogateDiagTailX0RatChunk000Sub000Block171Part022
    + surrogateDiagTailX0RatChunk000Sub000Block171Part023
    + surrogateDiagTailX0RatChunk000Sub000Block171Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block171_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block171Head + surrogateDiagTailX0RatChunk000Sub000Block171Mid + surrogateDiagTailX0RatChunk000Sub000Block171Tail =
      surrogateDiagTailX0RatChunk000Sub000Block171 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block171Head surrogateDiagTailX0RatChunk000Sub000Block171Mid surrogateDiagTailX0RatChunk000Sub000Block171Tail surrogateDiagTailX0RatChunk000Sub000Block171
  ring

def SurrogateDiagonalTailChunk000Sub000Block171HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block171HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block171Head

def SurrogateDiagonalTailChunk000Sub000Block171MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block171MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block171Mid

def SurrogateDiagonalTailChunk000Sub000Block171TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block171TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block171Tail

theorem surrogateDiagonalTailChunk000Sub000Block171_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block171HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block171MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block171TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block171Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block171 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block171HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block171MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block171TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block171Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block171_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
