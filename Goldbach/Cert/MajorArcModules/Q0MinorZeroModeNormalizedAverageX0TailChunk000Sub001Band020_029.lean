import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [20,30). -/

/-- Block 020 covers tail-support indices [5500,5525) and q from 9094 to 9133. -/

def TailChunk000Sub001Block020Part000SupportExplicit : Finset ℕ :=
  ([9094] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part000 : ℚ :=
  (2583884244775 : ℚ) / 1067934420488902728

def SurrogateDiagonalTailChunk000Sub001Block020Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9094
    = surrogateDiagTailX0RatChunk000Sub001Block020Part000

theorem surrogateDiagonalTailChunk000Sub001Block020Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part000] using hcert

def TailChunk000Sub001Block020Part001SupportExplicit : Finset ℕ :=
  ([9095] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part001 : ℚ :=
  (842842503625 : ℚ) / 1324067801417121792

def SurrogateDiagonalTailChunk000Sub001Block020Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9095
    = surrogateDiagTailX0RatChunk000Sub001Block020Part001

theorem surrogateDiagonalTailChunk000Sub001Block020Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part001] using hcert

def TailChunk000Sub001Block020Part002SupportExplicit : Finset ℕ :=
  ([9097] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part002 : ℚ :=
  (2987493573 : ℚ) / 7759894004733920

def SurrogateDiagonalTailChunk000Sub001Block020Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9097
    = surrogateDiagTailX0RatChunk000Sub001Block020Part002

theorem surrogateDiagonalTailChunk000Sub001Block020Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part002] using hcert

def TailChunk000Sub001Block020Part003SupportExplicit : Finset ℕ :=
  ([9098] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part003 : ℚ :=
  (2586157789975 : ℚ) / 1069815000127022208

def SurrogateDiagonalTailChunk000Sub001Block020Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9098
    = surrogateDiagTailX0RatChunk000Sub001Block020Part003

theorem surrogateDiagonalTailChunk000Sub001Block020Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part003] using hcert

def TailChunk000Sub001Block020Part004SupportExplicit : Finset ℕ :=
  ([9101] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part004 : ℚ :=
  (1193993901175 : ℚ) / 3425851032175955232

def SurrogateDiagonalTailChunk000Sub001Block020Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9101
    = surrogateDiagTailX0RatChunk000Sub001Block020Part004

theorem surrogateDiagonalTailChunk000Sub001Block020Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part004] using hcert

def TailChunk000Sub001Block020Part005SupportExplicit : Finset ℕ :=
  ([9102] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part005 : ℚ :=
  (16466841029 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub001Block020Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9102
    = surrogateDiagTailX0RatChunk000Sub001Block020Part005

theorem surrogateDiagonalTailChunk000Sub001Block020Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part005] using hcert

def TailChunk000Sub001Block020Part006SupportExplicit : Finset ℕ :=
  ([9103] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part006 : ℚ :=
  (1294759515625 : ℚ) / 4290562100663976402

def SurrogateDiagonalTailChunk000Sub001Block020Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9103
    = surrogateDiagTailX0RatChunk000Sub001Block020Part006

theorem surrogateDiagonalTailChunk000Sub001Block020Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part006] using hcert

def TailChunk000Sub001Block020Part007SupportExplicit : Finset ℕ :=
  ([9105] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part007 : ℚ :=
  (2114449897225 : ℚ) / 1381265942035857408

def SurrogateDiagonalTailChunk000Sub001Block020Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9105
    = surrogateDiagTailX0RatChunk000Sub001Block020Part007

theorem surrogateDiagonalTailChunk000Sub001Block020Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part007] using hcert

def TailChunk000Sub001Block020Part008SupportExplicit : Finset ℕ :=
  ([9106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part008 : ℚ :=
  (1248540911725 : ℚ) / 910243062639525888

def SurrogateDiagonalTailChunk000Sub001Block020Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9106
    = surrogateDiagTailX0RatChunk000Sub001Block020Part008

theorem surrogateDiagonalTailChunk000Sub001Block020Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part008] using hcert

def TailChunk000Sub001Block020Part009SupportExplicit : Finset ℕ :=
  ([9107] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part009 : ℚ :=
  (9159734531 : ℚ) / 20568032784000000

def SurrogateDiagonalTailChunk000Sub001Block020Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9107
    = surrogateDiagTailX0RatChunk000Sub001Block020Part009

theorem surrogateDiagonalTailChunk000Sub001Block020Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part009] using hcert

def TailChunk000Sub001Block020Part010SupportExplicit : Finset ℕ :=
  ([9109] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part010 : ℚ :=
  (1296466890625 : ℚ) / 4301886573824270112

def SurrogateDiagonalTailChunk000Sub001Block020Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9109
    = surrogateDiagTailX0RatChunk000Sub001Block020Part010

theorem surrogateDiagonalTailChunk000Sub001Block020Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part010] using hcert

def TailChunk000Sub001Block020Part011SupportExplicit : Finset ℕ :=
  ([9110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part011 : ℚ :=
  (2902234929 : ℚ) / 1170580070266880

def SurrogateDiagonalTailChunk000Sub001Block020Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9110
    = surrogateDiagTailX0RatChunk000Sub001Block020Part011

theorem surrogateDiagonalTailChunk000Sub001Block020Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part011] using hcert

def TailChunk000Sub001Block020Part012SupportExplicit : Finset ℕ :=
  ([9111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part012 : ℚ :=
  (1440745363175 : ℚ) / 1699510745214526464

def SurrogateDiagonalTailChunk000Sub001Block020Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9111
    = surrogateDiagTailX0RatChunk000Sub001Block020Part012

theorem surrogateDiagonalTailChunk000Sub001Block020Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part012] using hcert

def TailChunk000Sub001Block020Part013SupportExplicit : Finset ℕ :=
  ([9113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part013 : ℚ :=
  (183927716551 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk000Sub001Block020Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9113
    = surrogateDiagTailX0RatChunk000Sub001Block020Part013

theorem surrogateDiagonalTailChunk000Sub001Block020Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part013] using hcert

def TailChunk000Sub001Block020Part014SupportExplicit : Finset ℕ :=
  ([9115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part014 : ℚ :=
  (1245491917275 : ℚ) / 2351467929648633856

def SurrogateDiagonalTailChunk000Sub001Block020Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9115
    = surrogateDiagTailX0RatChunk000Sub001Block020Part014

theorem surrogateDiagonalTailChunk000Sub001Block020Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part014] using hcert

def TailChunk000Sub001Block020Part015SupportExplicit : Finset ℕ :=
  ([9118] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part015 : ℚ :=
  (631315380875 : ℚ) / 475459054190198784

def SurrogateDiagonalTailChunk000Sub001Block020Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9118
    = surrogateDiagTailX0RatChunk000Sub001Block020Part015

theorem surrogateDiagonalTailChunk000Sub001Block020Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part015] using hcert

def TailChunk000Sub001Block020Part016SupportExplicit : Finset ℕ :=
  ([9119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part016 : ℚ :=
  (18011809669 : ℚ) / 47011942614021120

def SurrogateDiagonalTailChunk000Sub001Block020Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9119
    = surrogateDiagTailX0RatChunk000Sub001Block020Part016

theorem surrogateDiagonalTailChunk000Sub001Block020Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part016] using hcert

def TailChunk000Sub001Block020Part017SupportExplicit : Finset ℕ :=
  ([9121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part017 : ℚ :=
  (229698179975 : ℚ) / 517372442088538176

def SurrogateDiagonalTailChunk000Sub001Block020Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9121
    = surrogateDiagTailX0RatChunk000Sub001Block020Part017

theorem surrogateDiagonalTailChunk000Sub001Block020Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part017] using hcert

def TailChunk000Sub001Block020Part018SupportExplicit : Finset ℕ :=
  ([9122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part018 : ℚ :=
  (520068025 : ℚ) / 432460275720192

def SurrogateDiagonalTailChunk000Sub001Block020Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9122
    = surrogateDiagTailX0RatChunk000Sub001Block020Part018

theorem surrogateDiagonalTailChunk000Sub001Block020Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part018] using hcert

def TailChunk000Sub001Block020Part019SupportExplicit : Finset ℕ :=
  ([9123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part019 : ℚ :=
  (57781738829 : ℚ) / 68339401595289600

def SurrogateDiagonalTailChunk000Sub001Block020Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9123
    = surrogateDiagTailX0RatChunk000Sub001Block020Part019

theorem surrogateDiagonalTailChunk000Sub001Block020Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part019] using hcert

def TailChunk000Sub001Block020Part020SupportExplicit : Finset ℕ :=
  ([9127] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part020 : ℚ :=
  (1301595765625 : ℚ) / 4335994526489807922

def SurrogateDiagonalTailChunk000Sub001Block020Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9127
    = surrogateDiagTailX0RatChunk000Sub001Block020Part020

theorem surrogateDiagonalTailChunk000Sub001Block020Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part020] using hcert

def TailChunk000Sub001Block020Part021SupportExplicit : Finset ℕ :=
  ([9129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part021 : ℚ :=
  (2138635049275 : ℚ) / 2632126644017430528

def SurrogateDiagonalTailChunk000Sub001Block020Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9129
    = surrogateDiagTailX0RatChunk000Sub001Block020Part021

theorem surrogateDiagonalTailChunk000Sub001Block020Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part021] using hcert

def TailChunk000Sub001Block020Part022SupportExplicit : Finset ℕ :=
  ([9130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part022 : ℚ :=
  (1645190199 : ℚ) / 482359663308800

def SurrogateDiagonalTailChunk000Sub001Block020Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9130
    = surrogateDiagTailX0RatChunk000Sub001Block020Part022

theorem surrogateDiagonalTailChunk000Sub001Block020Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part022] using hcert

def TailChunk000Sub001Block020Part023SupportExplicit : Finset ℕ :=
  ([9131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part023 : ℚ :=
  (2434451935325 : ℚ) / 7202252287818998784

def SurrogateDiagonalTailChunk000Sub001Block020Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9131
    = surrogateDiagTailX0RatChunk000Sub001Block020Part023

theorem surrogateDiagonalTailChunk000Sub001Block020Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part023] using hcert

def TailChunk000Sub001Block020Part024SupportExplicit : Finset ℕ :=
  ([9133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block020Part024 : ℚ :=
  (1303307640625 : ℚ) / 4347408786923165472

def SurrogateDiagonalTailChunk000Sub001Block020Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9133
    = surrogateDiagTailX0RatChunk000Sub001Block020Part024

theorem surrogateDiagonalTailChunk000Sub001Block020Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block020Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block020Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block020Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block020Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block020Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block020HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block020Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block020Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block020Part000
    + surrogateDiagTailX0RatChunk000Sub001Block020Part001
    + surrogateDiagTailX0RatChunk000Sub001Block020Part002
    + surrogateDiagTailX0RatChunk000Sub001Block020Part003
    + surrogateDiagTailX0RatChunk000Sub001Block020Part004
    + surrogateDiagTailX0RatChunk000Sub001Block020Part005
    + surrogateDiagTailX0RatChunk000Sub001Block020Part006
    + surrogateDiagTailX0RatChunk000Sub001Block020Part007
    + surrogateDiagTailX0RatChunk000Sub001Block020Part008
    + surrogateDiagTailX0RatChunk000Sub001Block020Part009

def surrogateDiagonalTailChunk000Sub001Block020MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block020Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block020Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block020Part010
    + surrogateDiagTailX0RatChunk000Sub001Block020Part011
    + surrogateDiagTailX0RatChunk000Sub001Block020Part012
    + surrogateDiagTailX0RatChunk000Sub001Block020Part013
    + surrogateDiagTailX0RatChunk000Sub001Block020Part014
    + surrogateDiagTailX0RatChunk000Sub001Block020Part015
    + surrogateDiagTailX0RatChunk000Sub001Block020Part016
    + surrogateDiagTailX0RatChunk000Sub001Block020Part017
    + surrogateDiagTailX0RatChunk000Sub001Block020Part018
    + surrogateDiagTailX0RatChunk000Sub001Block020Part019

def surrogateDiagonalTailChunk000Sub001Block020TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block020Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block020Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block020Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block020Part020
    + surrogateDiagTailX0RatChunk000Sub001Block020Part021
    + surrogateDiagTailX0RatChunk000Sub001Block020Part022
    + surrogateDiagTailX0RatChunk000Sub001Block020Part023
    + surrogateDiagTailX0RatChunk000Sub001Block020Part024

def surrogateDiagonalTailChunk000Sub001Block020Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block020HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block020MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block020TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block020 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block020Part000
    + surrogateDiagTailX0RatChunk000Sub001Block020Part001
    + surrogateDiagTailX0RatChunk000Sub001Block020Part002
    + surrogateDiagTailX0RatChunk000Sub001Block020Part003
    + surrogateDiagTailX0RatChunk000Sub001Block020Part004
    + surrogateDiagTailX0RatChunk000Sub001Block020Part005
    + surrogateDiagTailX0RatChunk000Sub001Block020Part006
    + surrogateDiagTailX0RatChunk000Sub001Block020Part007
    + surrogateDiagTailX0RatChunk000Sub001Block020Part008
    + surrogateDiagTailX0RatChunk000Sub001Block020Part009
    + surrogateDiagTailX0RatChunk000Sub001Block020Part010
    + surrogateDiagTailX0RatChunk000Sub001Block020Part011
    + surrogateDiagTailX0RatChunk000Sub001Block020Part012
    + surrogateDiagTailX0RatChunk000Sub001Block020Part013
    + surrogateDiagTailX0RatChunk000Sub001Block020Part014
    + surrogateDiagTailX0RatChunk000Sub001Block020Part015
    + surrogateDiagTailX0RatChunk000Sub001Block020Part016
    + surrogateDiagTailX0RatChunk000Sub001Block020Part017
    + surrogateDiagTailX0RatChunk000Sub001Block020Part018
    + surrogateDiagTailX0RatChunk000Sub001Block020Part019
    + surrogateDiagTailX0RatChunk000Sub001Block020Part020
    + surrogateDiagTailX0RatChunk000Sub001Block020Part021
    + surrogateDiagTailX0RatChunk000Sub001Block020Part022
    + surrogateDiagTailX0RatChunk000Sub001Block020Part023
    + surrogateDiagTailX0RatChunk000Sub001Block020Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block020_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block020Head + surrogateDiagTailX0RatChunk000Sub001Block020Mid + surrogateDiagTailX0RatChunk000Sub001Block020Tail =
      surrogateDiagTailX0RatChunk000Sub001Block020 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block020Head surrogateDiagTailX0RatChunk000Sub001Block020Mid surrogateDiagTailX0RatChunk000Sub001Block020Tail surrogateDiagTailX0RatChunk000Sub001Block020
  ring

def SurrogateDiagonalTailChunk000Sub001Block020HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block020HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block020Head

def SurrogateDiagonalTailChunk000Sub001Block020MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block020MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block020Mid

def SurrogateDiagonalTailChunk000Sub001Block020TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block020TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block020Tail

theorem surrogateDiagonalTailChunk000Sub001Block020_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block020HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block020MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block020TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block020Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block020 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block020HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block020MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block020TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block020Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block020_eq_head_add_mid_add_tail

/-- Block 021 covers tail-support indices [5525,5550) and q from 9134 to 9174. -/

def TailChunk000Sub001Block021Part000SupportExplicit : Finset ℕ :=
  ([9134] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part000 : ℚ :=
  (325898265625 : ℚ) / 271713049182697842

def SurrogateDiagonalTailChunk000Sub001Block021Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9134
    = surrogateDiagTailX0RatChunk000Sub001Block021Part000

theorem surrogateDiagonalTailChunk000Sub001Block021Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part000] using hcert

def TailChunk000Sub001Block021Part001SupportExplicit : Finset ℕ :=
  ([9137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part001 : ℚ :=
  (1304449515625 : ℚ) / 4355030803568074752

def SurrogateDiagonalTailChunk000Sub001Block021Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9137
    = surrogateDiagTailX0RatChunk000Sub001Block021Part001

theorem surrogateDiagonalTailChunk000Sub001Block021Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part001] using hcert

def TailChunk000Sub001Block021Part002SupportExplicit : Finset ℕ :=
  ([9138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part002 : ℚ :=
  (86930625 : ℚ) / 21464392489024

def SurrogateDiagonalTailChunk000Sub001Block021Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9138
    = surrogateDiagTailX0RatChunk000Sub001Block021Part002

theorem surrogateDiagonalTailChunk000Sub001Block021Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part002] using hcert

def TailChunk000Sub001Block021Part003SupportExplicit : Finset ℕ :=
  ([9139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part003 : ℚ :=
  (457273556825 : ℚ) / 1015802686597496832

def SurrogateDiagonalTailChunk000Sub001Block021Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9139
    = surrogateDiagTailX0RatChunk000Sub001Block021Part003

theorem surrogateDiagonalTailChunk000Sub001Block021Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part003] using hcert

def TailChunk000Sub001Block021Part004SupportExplicit : Finset ℕ :=
  ([9141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part004 : ℚ :=
  (82517479951 : ℚ) / 92863096521523200

def SurrogateDiagonalTailChunk000Sub001Block021Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9141
    = surrogateDiagTailX0RatChunk000Sub001Block021Part004

theorem surrogateDiagonalTailChunk000Sub001Block021Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part004] using hcert

def TailChunk000Sub001Block021Part005SupportExplicit : Finset ℕ :=
  ([9142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part005 : ℚ :=
  (286140584125 : ℚ) / 146407138333512192

def SurrogateDiagonalTailChunk000Sub001Block021Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9142
    = surrogateDiagTailX0RatChunk000Sub001Block021Part005

theorem surrogateDiagonalTailChunk000Sub001Block021Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part005] using hcert

def TailChunk000Sub001Block021Part006SupportExplicit : Finset ℕ :=
  ([9143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part006 : ℚ :=
  (66750209021 : ℚ) / 207308666754662400

def SurrogateDiagonalTailChunk000Sub001Block021Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9143
    = surrogateDiagTailX0RatChunk000Sub001Block021Part006

theorem surrogateDiagonalTailChunk000Sub001Block021Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part006] using hcert

def TailChunk000Sub001Block021Part007SupportExplicit : Finset ℕ :=
  ([9145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part007 : ℚ :=
  (140454942901 : ℚ) / 234705792828211200

def SurrogateDiagonalTailChunk000Sub001Block021Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9145
    = surrogateDiagTailX0RatChunk000Sub001Block021Part007

theorem surrogateDiagonalTailChunk000Sub001Block021Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part007] using hcert

def TailChunk000Sub001Block021Part008SupportExplicit : Finset ℕ :=
  ([9146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part008 : ℚ :=
  (308802619525 : ℚ) / 211342078500667392

def SurrogateDiagonalTailChunk000Sub001Block021Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9146
    = surrogateDiagTailX0RatChunk000Sub001Block021Part008

theorem surrogateDiagonalTailChunk000Sub001Block021Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part008] using hcert

def TailChunk000Sub001Block021Part009SupportExplicit : Finset ℕ :=
  ([9147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part009 : ℚ :=
  (1452154688225 : ℚ) / 1726540207241969664

def SurrogateDiagonalTailChunk000Sub001Block021Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9147
    = surrogateDiagTailX0RatChunk000Sub001Block021Part009

theorem surrogateDiagonalTailChunk000Sub001Block021Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part009] using hcert

def TailChunk000Sub001Block021Part010SupportExplicit : Finset ℕ :=
  ([9149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part010 : ℚ :=
  (231111063875 : ℚ) / 523759680599201856

def SurrogateDiagonalTailChunk000Sub001Block021Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9149
    = surrogateDiagTailX0RatChunk000Sub001Block021Part010

theorem surrogateDiagonalTailChunk000Sub001Block021Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part010] using hcert

def TailChunk000Sub001Block021Part011SupportExplicit : Finset ℕ :=
  ([9151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part011 : ℚ :=
  (83740801 : ℚ) / 280434355906050

def SurrogateDiagonalTailChunk000Sub001Block021Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9151
    = surrogateDiagTailX0RatChunk000Sub001Block021Part011

theorem surrogateDiagonalTailChunk000Sub001Block021Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part011] using hcert

def TailChunk000Sub001Block021Part012SupportExplicit : Finset ℕ :=
  ([9154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part012 : ℚ :=
  (312951732475 : ℚ) / 225070383994343712

def SurrogateDiagonalTailChunk000Sub001Block021Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9154
    = surrogateDiagTailX0RatChunk000Sub001Block021Part012

theorem surrogateDiagonalTailChunk000Sub001Block021Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part012] using hcert

def TailChunk000Sub001Block021Part013SupportExplicit : Finset ℕ :=
  ([9155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part013 : ℚ :=
  (142391658589 : ℚ) / 287164780447795200

def SurrogateDiagonalTailChunk000Sub001Block021Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9155
    = surrogateDiagTailX0RatChunk000Sub001Block021Part013

theorem surrogateDiagonalTailChunk000Sub001Block021Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part013] using hcert

def TailChunk000Sub001Block021Part014SupportExplicit : Finset ℕ :=
  ([9157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part014 : ℚ :=
  (1310166390625 : ℚ) / 4393291332080462112

def SurrogateDiagonalTailChunk000Sub001Block021Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9157
    = surrogateDiagTailX0RatChunk000Sub001Block021Part014

theorem surrogateDiagonalTailChunk000Sub001Block021Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part014] using hcert

def TailChunk000Sub001Block021Part015SupportExplicit : Finset ℕ :=
  ([9158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part015 : ℚ :=
  (49769852761 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block021Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9158
    = surrogateDiagTailX0RatChunk000Sub001Block021Part015

theorem surrogateDiagonalTailChunk000Sub001Block021Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part015] using hcert

def TailChunk000Sub001Block021Part016SupportExplicit : Finset ℕ :=
  ([9159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part016 : ℚ :=
  (110737739407 : ℚ) / 119562821318707200

def SurrogateDiagonalTailChunk000Sub001Block021Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9159
    = surrogateDiagTailX0RatChunk000Sub001Block021Part016

theorem surrogateDiagonalTailChunk000Sub001Block021Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part016] using hcert

def TailChunk000Sub001Block021Part017SupportExplicit : Finset ℕ :=
  ([9161] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part017 : ℚ :=
  (2098098025 : ℚ) / 7041557741302272

def SurrogateDiagonalTailChunk000Sub001Block021Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9161
    = surrogateDiagTailX0RatChunk000Sub001Block021Part017

theorem surrogateDiagonalTailChunk000Sub001Block021Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part017] using hcert

def TailChunk000Sub001Block021Part018SupportExplicit : Finset ℕ :=
  ([9165] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part018 : ℚ :=
  (235034577575 : ℚ) / 118864763547549696

def SurrogateDiagonalTailChunk000Sub001Block021Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9165
    = surrogateDiagTailX0RatChunk000Sub001Block021Part018

theorem surrogateDiagonalTailChunk000Sub001Block021Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part018] using hcert

def TailChunk000Sub001Block021Part019SupportExplicit : Finset ℕ :=
  ([9166] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part019 : ℚ :=
  (328185765625 : ℚ) / 275541619702089522

def SurrogateDiagonalTailChunk000Sub001Block021Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9166
    = surrogateDiagTailX0RatChunk000Sub001Block021Part019

theorem surrogateDiagonalTailChunk000Sub001Block021Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part019] using hcert

def TailChunk000Sub001Block021Part020SupportExplicit : Finset ℕ :=
  ([9167] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part020 : ℚ :=
  (231559596775 : ℚ) / 737794738381307904

def SurrogateDiagonalTailChunk000Sub001Block021Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9167
    = surrogateDiagTailX0RatChunk000Sub001Block021Part020

theorem surrogateDiagonalTailChunk000Sub001Block021Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part020] using hcert

def TailChunk000Sub001Block021Part021SupportExplicit : Finset ℕ :=
  ([9169] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part021 : ℚ :=
  (5068460432725 : ℚ) / 16001254070038069248

def SurrogateDiagonalTailChunk000Sub001Block021Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9169
    = surrogateDiagTailX0RatChunk000Sub001Block021Part021

theorem surrogateDiagonalTailChunk000Sub001Block021Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part021] using hcert

def TailChunk000Sub001Block021Part022SupportExplicit : Finset ℕ :=
  ([9170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part022 : ℚ :=
  (3991327991 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub001Block021Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9170
    = surrogateDiagTailX0RatChunk000Sub001Block021Part022

theorem surrogateDiagonalTailChunk000Sub001Block021Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part022] using hcert

def TailChunk000Sub001Block021Part023SupportExplicit : Finset ℕ :=
  ([9173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part023 : ℚ :=
  (1314748890625 : ℚ) / 4424080816323577632

def SurrogateDiagonalTailChunk000Sub001Block021Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9173
    = surrogateDiagTailX0RatChunk000Sub001Block021Part023

theorem surrogateDiagonalTailChunk000Sub001Block021Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part023] using hcert

def TailChunk000Sub001Block021Part024SupportExplicit : Finset ℕ :=
  ([9174] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block021Part024 : ℚ :=
  (15981731927 : ℚ) / 2901971766297600

def SurrogateDiagonalTailChunk000Sub001Block021Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9174
    = surrogateDiagTailX0RatChunk000Sub001Block021Part024

theorem surrogateDiagonalTailChunk000Sub001Block021Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block021Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block021Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block021Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block021Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block021Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block021HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block021Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block021Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block021Part000
    + surrogateDiagTailX0RatChunk000Sub001Block021Part001
    + surrogateDiagTailX0RatChunk000Sub001Block021Part002
    + surrogateDiagTailX0RatChunk000Sub001Block021Part003
    + surrogateDiagTailX0RatChunk000Sub001Block021Part004
    + surrogateDiagTailX0RatChunk000Sub001Block021Part005
    + surrogateDiagTailX0RatChunk000Sub001Block021Part006
    + surrogateDiagTailX0RatChunk000Sub001Block021Part007
    + surrogateDiagTailX0RatChunk000Sub001Block021Part008
    + surrogateDiagTailX0RatChunk000Sub001Block021Part009

def surrogateDiagonalTailChunk000Sub001Block021MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block021Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block021Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block021Part010
    + surrogateDiagTailX0RatChunk000Sub001Block021Part011
    + surrogateDiagTailX0RatChunk000Sub001Block021Part012
    + surrogateDiagTailX0RatChunk000Sub001Block021Part013
    + surrogateDiagTailX0RatChunk000Sub001Block021Part014
    + surrogateDiagTailX0RatChunk000Sub001Block021Part015
    + surrogateDiagTailX0RatChunk000Sub001Block021Part016
    + surrogateDiagTailX0RatChunk000Sub001Block021Part017
    + surrogateDiagTailX0RatChunk000Sub001Block021Part018
    + surrogateDiagTailX0RatChunk000Sub001Block021Part019

def surrogateDiagonalTailChunk000Sub001Block021TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block021Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block021Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block021Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block021Part020
    + surrogateDiagTailX0RatChunk000Sub001Block021Part021
    + surrogateDiagTailX0RatChunk000Sub001Block021Part022
    + surrogateDiagTailX0RatChunk000Sub001Block021Part023
    + surrogateDiagTailX0RatChunk000Sub001Block021Part024

def surrogateDiagonalTailChunk000Sub001Block021Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block021HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block021MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block021TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block021 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block021Part000
    + surrogateDiagTailX0RatChunk000Sub001Block021Part001
    + surrogateDiagTailX0RatChunk000Sub001Block021Part002
    + surrogateDiagTailX0RatChunk000Sub001Block021Part003
    + surrogateDiagTailX0RatChunk000Sub001Block021Part004
    + surrogateDiagTailX0RatChunk000Sub001Block021Part005
    + surrogateDiagTailX0RatChunk000Sub001Block021Part006
    + surrogateDiagTailX0RatChunk000Sub001Block021Part007
    + surrogateDiagTailX0RatChunk000Sub001Block021Part008
    + surrogateDiagTailX0RatChunk000Sub001Block021Part009
    + surrogateDiagTailX0RatChunk000Sub001Block021Part010
    + surrogateDiagTailX0RatChunk000Sub001Block021Part011
    + surrogateDiagTailX0RatChunk000Sub001Block021Part012
    + surrogateDiagTailX0RatChunk000Sub001Block021Part013
    + surrogateDiagTailX0RatChunk000Sub001Block021Part014
    + surrogateDiagTailX0RatChunk000Sub001Block021Part015
    + surrogateDiagTailX0RatChunk000Sub001Block021Part016
    + surrogateDiagTailX0RatChunk000Sub001Block021Part017
    + surrogateDiagTailX0RatChunk000Sub001Block021Part018
    + surrogateDiagTailX0RatChunk000Sub001Block021Part019
    + surrogateDiagTailX0RatChunk000Sub001Block021Part020
    + surrogateDiagTailX0RatChunk000Sub001Block021Part021
    + surrogateDiagTailX0RatChunk000Sub001Block021Part022
    + surrogateDiagTailX0RatChunk000Sub001Block021Part023
    + surrogateDiagTailX0RatChunk000Sub001Block021Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block021_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block021Head + surrogateDiagTailX0RatChunk000Sub001Block021Mid + surrogateDiagTailX0RatChunk000Sub001Block021Tail =
      surrogateDiagTailX0RatChunk000Sub001Block021 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block021Head surrogateDiagTailX0RatChunk000Sub001Block021Mid surrogateDiagTailX0RatChunk000Sub001Block021Tail surrogateDiagTailX0RatChunk000Sub001Block021
  ring

def SurrogateDiagonalTailChunk000Sub001Block021HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block021HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block021Head

def SurrogateDiagonalTailChunk000Sub001Block021MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block021MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block021Mid

def SurrogateDiagonalTailChunk000Sub001Block021TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block021TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block021Tail

theorem surrogateDiagonalTailChunk000Sub001Block021_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block021HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block021MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block021TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block021Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block021 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block021HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block021MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block021TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block021Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block021_eq_head_add_mid_add_tail

/-- Block 022 covers tail-support indices [5550,5575) and q from 9177 to 9213. -/

def TailChunk000Sub001Block022Part000SupportExplicit : Finset ℕ :=
  ([9177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part000 : ℚ :=
  (2074408448125 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub001Block022Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9177
    = surrogateDiagTailX0RatChunk000Sub001Block022Part000

theorem surrogateDiagonalTailChunk000Sub001Block022Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part000] using hcert

def TailChunk000Sub001Block022Part001SupportExplicit : Finset ℕ :=
  ([9178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part001 : ℚ :=
  (1163588132075 : ℚ) / 398008641329823744

def SurrogateDiagonalTailChunk000Sub001Block022Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9178
    = surrogateDiagTailX0RatChunk000Sub001Block022Part001

theorem surrogateDiagonalTailChunk000Sub001Block022Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part001] using hcert

def TailChunk000Sub001Block022Part002SupportExplicit : Finset ℕ :=
  ([9179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part002 : ℚ :=
  (566490550375 : ℚ) / 1803498249376530432

def SurrogateDiagonalTailChunk000Sub001Block022Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9179
    = surrogateDiagTailX0RatChunk000Sub001Block022Part002

theorem surrogateDiagonalTailChunk000Sub001Block022Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part002] using hcert

def TailChunk000Sub001Block022Part003SupportExplicit : Finset ℕ :=
  ([9181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part003 : ℚ :=
  (2107269025 : ℚ) / 7103257769240352

def SurrogateDiagonalTailChunk000Sub001Block022Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9181
    = surrogateDiagTailX0RatChunk000Sub001Block022Part003

theorem surrogateDiagonalTailChunk000Sub001Block022Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part003] using hcert

def TailChunk000Sub001Block022Part004SupportExplicit : Finset ℕ :=
  ([9182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part004 : ℚ :=
  (526932025 : ℚ) / 443953610577522

def SurrogateDiagonalTailChunk000Sub001Block022Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9182
    = surrogateDiagTailX0RatChunk000Sub001Block022Part004

theorem surrogateDiagonalTailChunk000Sub001Block022Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part004] using hcert

def TailChunk000Sub001Block022Part005SupportExplicit : Finset ℕ :=
  ([9183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part005 : ℚ :=
  (585850111 : ℚ) / 3507781614439680

def SurrogateDiagonalTailChunk000Sub001Block022Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9183
    = surrogateDiagTailX0RatChunk000Sub001Block022Part005

theorem surrogateDiagonalTailChunk000Sub001Block022Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part005] using hcert

def TailChunk000Sub001Block022Part006SupportExplicit : Finset ℕ :=
  ([9185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part006 : ℚ :=
  (7444977927 : ℚ) / 64809386890854400

def SurrogateDiagonalTailChunk000Sub001Block022Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9185
    = surrogateDiagTailX0RatChunk000Sub001Block022Part006

theorem surrogateDiagonalTailChunk000Sub001Block022Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part006] using hcert

def TailChunk000Sub001Block022Part007SupportExplicit : Finset ℕ :=
  ([9186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part007 : ℚ :=
  (68899 : ℚ) / 17191569600

def SurrogateDiagonalTailChunk000Sub001Block022Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9186
    = surrogateDiagTailX0RatChunk000Sub001Block022Part007

theorem surrogateDiagonalTailChunk000Sub001Block022Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part007] using hcert

def TailChunk000Sub001Block022Part008SupportExplicit : Finset ℕ :=
  ([9187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block022Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9187
    = surrogateDiagTailX0RatChunk000Sub001Block022Part008

theorem surrogateDiagonalTailChunk000Sub001Block022Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part008] using hcert

def TailChunk000Sub001Block022Part009SupportExplicit : Finset ℕ :=
  ([9190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part009 : ℚ :=
  (527432840375 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub001Block022Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9190
    = surrogateDiagTailX0RatChunk000Sub001Block022Part009

theorem surrogateDiagonalTailChunk000Sub001Block022Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part009] using hcert

def TailChunk000Sub001Block022Part010SupportExplicit : Finset ℕ :=
  ([9191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part010 : ℚ :=
  (835735847 : ℚ) / 9955270656000000

def SurrogateDiagonalTailChunk000Sub001Block022Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9191
    = surrogateDiagTailX0RatChunk000Sub001Block022Part010

theorem surrogateDiagonalTailChunk000Sub001Block022Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part010] using hcert

def TailChunk000Sub001Block022Part011SupportExplicit : Finset ℕ :=
  ([9193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part011 : ℚ :=
  (7734757925 : ℚ) / 1094660076220956672

def SurrogateDiagonalTailChunk000Sub001Block022Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9193
    = surrogateDiagTailX0RatChunk000Sub001Block022Part011

theorem surrogateDiagonalTailChunk000Sub001Block022Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part011] using hcert

def TailChunk000Sub001Block022Part012SupportExplicit : Finset ℕ :=
  ([9194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part012 : ℚ :=
  (330193890625 : ℚ) / 278924682645932832

def SurrogateDiagonalTailChunk000Sub001Block022Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9194
    = surrogateDiagTailX0RatChunk000Sub001Block022Part012

theorem surrogateDiagonalTailChunk000Sub001Block022Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part012] using hcert

def TailChunk000Sub001Block022Part013SupportExplicit : Finset ℕ :=
  ([9195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part013 : ℚ :=
  (751568264425 : ℚ) / 1436787349274492928

def SurrogateDiagonalTailChunk000Sub001Block022Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9195
    = surrogateDiagTailX0RatChunk000Sub001Block022Part013

theorem surrogateDiagonalTailChunk000Sub001Block022Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part013] using hcert

def TailChunk000Sub001Block022Part014SupportExplicit : Finset ℕ :=
  ([9197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part014 : ℚ :=
  (250015489 : ℚ) / 20643249232281600

def SurrogateDiagonalTailChunk000Sub001Block022Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9197
    = surrogateDiagTailX0RatChunk000Sub001Block022Part014

theorem surrogateDiagonalTailChunk000Sub001Block022Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part014] using hcert

def TailChunk000Sub001Block022Part015SupportExplicit : Finset ℕ :=
  ([9199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block022Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9199
    = surrogateDiagTailX0RatChunk000Sub001Block022Part015

theorem surrogateDiagonalTailChunk000Sub001Block022Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part015] using hcert

def TailChunk000Sub001Block022Part016SupportExplicit : Finset ℕ :=
  ([9201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part016 : ℚ :=
  (42010525775 : ℚ) / 252526760758060992

def SurrogateDiagonalTailChunk000Sub001Block022Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9201
    = surrogateDiagTailX0RatChunk000Sub001Block022Part016

theorem surrogateDiagonalTailChunk000Sub001Block022Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part016] using hcert

def TailChunk000Sub001Block022Part017SupportExplicit : Finset ℕ :=
  ([9202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part017 : ℚ :=
  (1284418085725 : ℚ) / 982307548856366208

def SurrogateDiagonalTailChunk000Sub001Block022Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9202
    = surrogateDiagTailX0RatChunk000Sub001Block022Part017

theorem surrogateDiagonalTailChunk000Sub001Block022Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part017] using hcert

def TailChunk000Sub001Block022Part018SupportExplicit : Finset ℕ :=
  ([9203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block022Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9203
    = surrogateDiagTailX0RatChunk000Sub001Block022Part018

theorem surrogateDiagonalTailChunk000Sub001Block022Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part018] using hcert

def TailChunk000Sub001Block022Part019SupportExplicit : Finset ℕ :=
  ([9205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part019 : ℚ :=
  (199160008975 : ℚ) / 977275473908539392

def SurrogateDiagonalTailChunk000Sub001Block022Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9205
    = surrogateDiagTailX0RatChunk000Sub001Block022Part019

theorem surrogateDiagonalTailChunk000Sub001Block022Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part019] using hcert

def TailChunk000Sub001Block022Part020SupportExplicit : Finset ℕ :=
  ([9206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part020 : ℚ :=
  (331056390625 : ℚ) / 280384063091508402

def SurrogateDiagonalTailChunk000Sub001Block022Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9206
    = surrogateDiagTailX0RatChunk000Sub001Block022Part020

theorem surrogateDiagonalTailChunk000Sub001Block022Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part020] using hcert

def TailChunk000Sub001Block022Part021SupportExplicit : Finset ℕ :=
  ([9209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block022Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9209
    = surrogateDiagTailX0RatChunk000Sub001Block022Part021

theorem surrogateDiagonalTailChunk000Sub001Block022Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part021] using hcert

def TailChunk000Sub001Block022Part022SupportExplicit : Finset ℕ :=
  ([9210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part022 : ℚ :=
  (728312449075 : ℚ) / 89799209329655808

def SurrogateDiagonalTailChunk000Sub001Block022Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9210
    = surrogateDiagTailX0RatChunk000Sub001Block022Part022

theorem surrogateDiagonalTailChunk000Sub001Block022Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part022] using hcert

def TailChunk000Sub001Block022Part023SupportExplicit : Finset ℕ :=
  ([9211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part023 : ℚ :=
  (518913233 : ℚ) / 131246244000000000

def SurrogateDiagonalTailChunk000Sub001Block022Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9211
    = surrogateDiagTailX0RatChunk000Sub001Block022Part023

theorem surrogateDiagonalTailChunk000Sub001Block022Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part023] using hcert

def TailChunk000Sub001Block022Part024SupportExplicit : Finset ℕ :=
  ([9213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block022Part024 : ℚ :=
  (1160947060225 : ℚ) / 3038171280930275328

def SurrogateDiagonalTailChunk000Sub001Block022Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9213
    = surrogateDiagTailX0RatChunk000Sub001Block022Part024

theorem surrogateDiagonalTailChunk000Sub001Block022Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block022Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block022Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block022Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block022Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block022Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block022HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block022Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block022Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block022Part000
    + surrogateDiagTailX0RatChunk000Sub001Block022Part001
    + surrogateDiagTailX0RatChunk000Sub001Block022Part002
    + surrogateDiagTailX0RatChunk000Sub001Block022Part003
    + surrogateDiagTailX0RatChunk000Sub001Block022Part004
    + surrogateDiagTailX0RatChunk000Sub001Block022Part005
    + surrogateDiagTailX0RatChunk000Sub001Block022Part006
    + surrogateDiagTailX0RatChunk000Sub001Block022Part007
    + surrogateDiagTailX0RatChunk000Sub001Block022Part008
    + surrogateDiagTailX0RatChunk000Sub001Block022Part009

def surrogateDiagonalTailChunk000Sub001Block022MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block022Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block022Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block022Part010
    + surrogateDiagTailX0RatChunk000Sub001Block022Part011
    + surrogateDiagTailX0RatChunk000Sub001Block022Part012
    + surrogateDiagTailX0RatChunk000Sub001Block022Part013
    + surrogateDiagTailX0RatChunk000Sub001Block022Part014
    + surrogateDiagTailX0RatChunk000Sub001Block022Part015
    + surrogateDiagTailX0RatChunk000Sub001Block022Part016
    + surrogateDiagTailX0RatChunk000Sub001Block022Part017
    + surrogateDiagTailX0RatChunk000Sub001Block022Part018
    + surrogateDiagTailX0RatChunk000Sub001Block022Part019

def surrogateDiagonalTailChunk000Sub001Block022TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block022Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block022Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block022Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block022Part020
    + surrogateDiagTailX0RatChunk000Sub001Block022Part021
    + surrogateDiagTailX0RatChunk000Sub001Block022Part022
    + surrogateDiagTailX0RatChunk000Sub001Block022Part023
    + surrogateDiagTailX0RatChunk000Sub001Block022Part024

def surrogateDiagonalTailChunk000Sub001Block022Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block022HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block022MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block022TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block022 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block022Part000
    + surrogateDiagTailX0RatChunk000Sub001Block022Part001
    + surrogateDiagTailX0RatChunk000Sub001Block022Part002
    + surrogateDiagTailX0RatChunk000Sub001Block022Part003
    + surrogateDiagTailX0RatChunk000Sub001Block022Part004
    + surrogateDiagTailX0RatChunk000Sub001Block022Part005
    + surrogateDiagTailX0RatChunk000Sub001Block022Part006
    + surrogateDiagTailX0RatChunk000Sub001Block022Part007
    + surrogateDiagTailX0RatChunk000Sub001Block022Part008
    + surrogateDiagTailX0RatChunk000Sub001Block022Part009
    + surrogateDiagTailX0RatChunk000Sub001Block022Part010
    + surrogateDiagTailX0RatChunk000Sub001Block022Part011
    + surrogateDiagTailX0RatChunk000Sub001Block022Part012
    + surrogateDiagTailX0RatChunk000Sub001Block022Part013
    + surrogateDiagTailX0RatChunk000Sub001Block022Part014
    + surrogateDiagTailX0RatChunk000Sub001Block022Part015
    + surrogateDiagTailX0RatChunk000Sub001Block022Part016
    + surrogateDiagTailX0RatChunk000Sub001Block022Part017
    + surrogateDiagTailX0RatChunk000Sub001Block022Part018
    + surrogateDiagTailX0RatChunk000Sub001Block022Part019
    + surrogateDiagTailX0RatChunk000Sub001Block022Part020
    + surrogateDiagTailX0RatChunk000Sub001Block022Part021
    + surrogateDiagTailX0RatChunk000Sub001Block022Part022
    + surrogateDiagTailX0RatChunk000Sub001Block022Part023
    + surrogateDiagTailX0RatChunk000Sub001Block022Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block022_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block022Head + surrogateDiagTailX0RatChunk000Sub001Block022Mid + surrogateDiagTailX0RatChunk000Sub001Block022Tail =
      surrogateDiagTailX0RatChunk000Sub001Block022 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block022Head surrogateDiagTailX0RatChunk000Sub001Block022Mid surrogateDiagTailX0RatChunk000Sub001Block022Tail surrogateDiagTailX0RatChunk000Sub001Block022
  ring

def SurrogateDiagonalTailChunk000Sub001Block022HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block022HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block022Head

def SurrogateDiagonalTailChunk000Sub001Block022MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block022MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block022Mid

def SurrogateDiagonalTailChunk000Sub001Block022TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block022TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block022Tail

theorem surrogateDiagonalTailChunk000Sub001Block022_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block022HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block022MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block022TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block022Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block022 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block022HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block022MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block022TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block022Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block022_eq_head_add_mid_add_tail

/-- Block 023 covers tail-support indices [5575,5600) and q from 9214 to 9254. -/

def TailChunk000Sub001Block023Part000SupportExplicit : Finset ℕ :=
  ([9214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part000 : ℚ :=
  (49963449787 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block023Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9214
    = surrogateDiagTailX0RatChunk000Sub001Block023Part000

theorem surrogateDiagonalTailChunk000Sub001Block023Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part000] using hcert

def TailChunk000Sub001Block023Part001SupportExplicit : Finset ℕ :=
  ([9215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part001 : ℚ :=
  (705094935175 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk000Sub001Block023Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9215
    = surrogateDiagTailX0RatChunk000Sub001Block023Part001

theorem surrogateDiagonalTailChunk000Sub001Block023Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part001] using hcert

def TailChunk000Sub001Block023Part002SupportExplicit : Finset ℕ :=
  ([9217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part002 : ℚ :=
  (55698071275 : ℚ) / 3257053426569388032

def SurrogateDiagonalTailChunk000Sub001Block023Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9217
    = surrogateDiagTailX0RatChunk000Sub001Block023Part002

theorem surrogateDiagonalTailChunk000Sub001Block023Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part002] using hcert

def TailChunk000Sub001Block023Part003SupportExplicit : Finset ℕ :=
  ([9218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part003 : ℚ :=
  (3241358679 : ℚ) / 2035638791415680

def SurrogateDiagonalTailChunk000Sub001Block023Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9218
    = surrogateDiagTailX0RatChunk000Sub001Block023Part003

theorem surrogateDiagonalTailChunk000Sub001Block023Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part003] using hcert

def TailChunk000Sub001Block023Part004SupportExplicit : Finset ℕ :=
  ([9219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part004 : ℚ :=
  (565290249425 : ℚ) / 954153591668941824

def SurrogateDiagonalTailChunk000Sub001Block023Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9219
    = surrogateDiagTailX0RatChunk000Sub001Block023Part004

theorem surrogateDiagonalTailChunk000Sub001Block023Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part004] using hcert

def TailChunk000Sub001Block023Part005SupportExplicit : Finset ℕ :=
  ([9221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block023Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9221
    = surrogateDiagTailX0RatChunk000Sub001Block023Part005

theorem surrogateDiagonalTailChunk000Sub001Block023Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part005] using hcert

def TailChunk000Sub001Block023Part006SupportExplicit : Finset ℕ :=
  ([9222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part006 : ℚ :=
  (281171595675 : ℚ) / 59933699597664256

def SurrogateDiagonalTailChunk000Sub001Block023Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9222
    = surrogateDiagTailX0RatChunk000Sub001Block023Part006

theorem surrogateDiagonalTailChunk000Sub001Block023Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part006] using hcert

def TailChunk000Sub001Block023Part007SupportExplicit : Finset ℕ :=
  ([9223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part007 : ℚ :=
  (1092411359 : ℚ) / 119963059814400000

def SurrogateDiagonalTailChunk000Sub001Block023Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9223
    = surrogateDiagTailX0RatChunk000Sub001Block023Part007

theorem surrogateDiagonalTailChunk000Sub001Block023Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part007] using hcert

def TailChunk000Sub001Block023Part008SupportExplicit : Finset ℕ :=
  ([9226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part008 : ℚ :=
  (291422553325 : ℚ) / 151871206657457952

def SurrogateDiagonalTailChunk000Sub001Block023Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9226
    = surrogateDiagTailX0RatChunk000Sub001Block023Part008

theorem surrogateDiagonalTailChunk000Sub001Block023Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part008] using hcert

def TailChunk000Sub001Block023Part009SupportExplicit : Finset ℕ :=
  ([9227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block023Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9227
    = surrogateDiagTailX0RatChunk000Sub001Block023Part009

theorem surrogateDiagonalTailChunk000Sub001Block023Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part009] using hcert

def TailChunk000Sub001Block023Part010SupportExplicit : Finset ℕ :=
  ([9229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part010 : ℚ :=
  (1064820103 : ℚ) / 49324526486310720

def SurrogateDiagonalTailChunk000Sub001Block023Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9229
    = surrogateDiagTailX0RatChunk000Sub001Block023Part010

theorem surrogateDiagonalTailChunk000Sub001Block023Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part010] using hcert

def TailChunk000Sub001Block023Part011SupportExplicit : Finset ℕ :=
  ([9230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part011 : ℚ :=
  (20408436023 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub001Block023Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9230
    = surrogateDiagTailX0RatChunk000Sub001Block023Part011

theorem surrogateDiagonalTailChunk000Sub001Block023Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part011] using hcert

def TailChunk000Sub001Block023Part012SupportExplicit : Finset ℕ :=
  ([9231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part012 : ℚ :=
  (15464829053 : ℚ) / 36699109746278400

def SurrogateDiagonalTailChunk000Sub001Block023Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9231
    = surrogateDiagTailX0RatChunk000Sub001Block023Part012

theorem surrogateDiagonalTailChunk000Sub001Block023Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part012] using hcert

def TailChunk000Sub001Block023Part013SupportExplicit : Finset ℕ :=
  ([9233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part013 : ℚ :=
  (18191949475 : ℚ) / 543276596040169536

def SurrogateDiagonalTailChunk000Sub001Block023Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9233
    = surrogateDiagTailX0RatChunk000Sub001Block023Part013

theorem surrogateDiagonalTailChunk000Sub001Block023Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part013] using hcert

def TailChunk000Sub001Block023Part014SupportExplicit : Finset ℕ :=
  ([9235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part014 : ℚ :=
  (79992658025 : ℚ) / 929188067385866496

def SurrogateDiagonalTailChunk000Sub001Block023Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9235
    = surrogateDiagTailX0RatChunk000Sub001Block023Part014

theorem surrogateDiagonalTailChunk000Sub001Block023Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part014] using hcert

def TailChunk000Sub001Block023Part015SupportExplicit : Finset ℕ :=
  ([9237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part015 : ℚ :=
  (592324232525 : ℚ) / 1795524385851676224

def SurrogateDiagonalTailChunk000Sub001Block023Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9237
    = surrogateDiagTailX0RatChunk000Sub001Block023Part015

theorem surrogateDiagonalTailChunk000Sub001Block023Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part015] using hcert

def TailChunk000Sub001Block023Part016SupportExplicit : Finset ℕ :=
  ([9238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part016 : ℚ :=
  (10294658927 : ℚ) / 7774075003299840

def SurrogateDiagonalTailChunk000Sub001Block023Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9238
    = surrogateDiagTailX0RatChunk000Sub001Block023Part016

theorem surrogateDiagonalTailChunk000Sub001Block023Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part016] using hcert

def TailChunk000Sub001Block023Part017SupportExplicit : Finset ℕ :=
  ([9239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block023Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9239
    = surrogateDiagTailX0RatChunk000Sub001Block023Part017

theorem surrogateDiagonalTailChunk000Sub001Block023Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part017] using hcert

def TailChunk000Sub001Block023Part018SupportExplicit : Finset ℕ :=
  ([9241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block023Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9241
    = surrogateDiagTailX0RatChunk000Sub001Block023Part018

theorem surrogateDiagonalTailChunk000Sub001Block023Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part018] using hcert

def TailChunk000Sub001Block023Part019SupportExplicit : Finset ℕ :=
  ([9242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part019 : ℚ :=
  (533841025 : ℚ) / 455674528042272

def SurrogateDiagonalTailChunk000Sub001Block023Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9242
    = surrogateDiagTailX0RatChunk000Sub001Block023Part019

theorem surrogateDiagonalTailChunk000Sub001Block023Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part019] using hcert

def TailChunk000Sub001Block023Part020SupportExplicit : Finset ℕ :=
  ([9246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part020 : ℚ :=
  (421746235325 : ℚ) / 88916694911345664

def SurrogateDiagonalTailChunk000Sub001Block023Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9246
    = surrogateDiagTailX0RatChunk000Sub001Block023Part020

theorem surrogateDiagonalTailChunk000Sub001Block023Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part020] using hcert

def TailChunk000Sub001Block023Part021SupportExplicit : Finset ℕ :=
  ([9247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part021 : ℚ :=
  (17488522813 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk000Sub001Block023Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9247
    = surrogateDiagTailX0RatChunk000Sub001Block023Part021

theorem surrogateDiagonalTailChunk000Sub001Block023Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part021] using hcert

def TailChunk000Sub001Block023Part022SupportExplicit : Finset ℕ :=
  ([9249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part022 : ℚ :=
  (297147680225 : ℚ) / 1804876055594032704

def SurrogateDiagonalTailChunk000Sub001Block023Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9249
    = surrogateDiagTailX0RatChunk000Sub001Block023Part022

theorem surrogateDiagonalTailChunk000Sub001Block023Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part022] using hcert

def TailChunk000Sub001Block023Part023SupportExplicit : Finset ℕ :=
  ([9253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part023 : ℚ :=
  (4249400675 : ℚ) / 406779872239146528

def SurrogateDiagonalTailChunk000Sub001Block023Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9253
    = surrogateDiagTailX0RatChunk000Sub001Block023Part023

theorem surrogateDiagonalTailChunk000Sub001Block023Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part023] using hcert

def TailChunk000Sub001Block023Part024SupportExplicit : Finset ℕ :=
  ([9254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block023Part024 : ℚ :=
  (169711241 : ℚ) / 91096948546560

def SurrogateDiagonalTailChunk000Sub001Block023Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9254
    = surrogateDiagTailX0RatChunk000Sub001Block023Part024

theorem surrogateDiagonalTailChunk000Sub001Block023Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block023Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block023Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block023Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block023Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block023Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block023HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block023Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block023Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block023Part000
    + surrogateDiagTailX0RatChunk000Sub001Block023Part001
    + surrogateDiagTailX0RatChunk000Sub001Block023Part002
    + surrogateDiagTailX0RatChunk000Sub001Block023Part003
    + surrogateDiagTailX0RatChunk000Sub001Block023Part004
    + surrogateDiagTailX0RatChunk000Sub001Block023Part005
    + surrogateDiagTailX0RatChunk000Sub001Block023Part006
    + surrogateDiagTailX0RatChunk000Sub001Block023Part007
    + surrogateDiagTailX0RatChunk000Sub001Block023Part008
    + surrogateDiagTailX0RatChunk000Sub001Block023Part009

def surrogateDiagonalTailChunk000Sub001Block023MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block023Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block023Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block023Part010
    + surrogateDiagTailX0RatChunk000Sub001Block023Part011
    + surrogateDiagTailX0RatChunk000Sub001Block023Part012
    + surrogateDiagTailX0RatChunk000Sub001Block023Part013
    + surrogateDiagTailX0RatChunk000Sub001Block023Part014
    + surrogateDiagTailX0RatChunk000Sub001Block023Part015
    + surrogateDiagTailX0RatChunk000Sub001Block023Part016
    + surrogateDiagTailX0RatChunk000Sub001Block023Part017
    + surrogateDiagTailX0RatChunk000Sub001Block023Part018
    + surrogateDiagTailX0RatChunk000Sub001Block023Part019

def surrogateDiagonalTailChunk000Sub001Block023TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block023Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block023Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block023Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block023Part020
    + surrogateDiagTailX0RatChunk000Sub001Block023Part021
    + surrogateDiagTailX0RatChunk000Sub001Block023Part022
    + surrogateDiagTailX0RatChunk000Sub001Block023Part023
    + surrogateDiagTailX0RatChunk000Sub001Block023Part024

def surrogateDiagonalTailChunk000Sub001Block023Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block023HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block023MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block023TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block023 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block023Part000
    + surrogateDiagTailX0RatChunk000Sub001Block023Part001
    + surrogateDiagTailX0RatChunk000Sub001Block023Part002
    + surrogateDiagTailX0RatChunk000Sub001Block023Part003
    + surrogateDiagTailX0RatChunk000Sub001Block023Part004
    + surrogateDiagTailX0RatChunk000Sub001Block023Part005
    + surrogateDiagTailX0RatChunk000Sub001Block023Part006
    + surrogateDiagTailX0RatChunk000Sub001Block023Part007
    + surrogateDiagTailX0RatChunk000Sub001Block023Part008
    + surrogateDiagTailX0RatChunk000Sub001Block023Part009
    + surrogateDiagTailX0RatChunk000Sub001Block023Part010
    + surrogateDiagTailX0RatChunk000Sub001Block023Part011
    + surrogateDiagTailX0RatChunk000Sub001Block023Part012
    + surrogateDiagTailX0RatChunk000Sub001Block023Part013
    + surrogateDiagTailX0RatChunk000Sub001Block023Part014
    + surrogateDiagTailX0RatChunk000Sub001Block023Part015
    + surrogateDiagTailX0RatChunk000Sub001Block023Part016
    + surrogateDiagTailX0RatChunk000Sub001Block023Part017
    + surrogateDiagTailX0RatChunk000Sub001Block023Part018
    + surrogateDiagTailX0RatChunk000Sub001Block023Part019
    + surrogateDiagTailX0RatChunk000Sub001Block023Part020
    + surrogateDiagTailX0RatChunk000Sub001Block023Part021
    + surrogateDiagTailX0RatChunk000Sub001Block023Part022
    + surrogateDiagTailX0RatChunk000Sub001Block023Part023
    + surrogateDiagTailX0RatChunk000Sub001Block023Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block023_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block023Head + surrogateDiagTailX0RatChunk000Sub001Block023Mid + surrogateDiagTailX0RatChunk000Sub001Block023Tail =
      surrogateDiagTailX0RatChunk000Sub001Block023 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block023Head surrogateDiagTailX0RatChunk000Sub001Block023Mid surrogateDiagTailX0RatChunk000Sub001Block023Tail surrogateDiagTailX0RatChunk000Sub001Block023
  ring

def SurrogateDiagonalTailChunk000Sub001Block023HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block023HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block023Head

def SurrogateDiagonalTailChunk000Sub001Block023MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block023MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block023Mid

def SurrogateDiagonalTailChunk000Sub001Block023TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block023TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block023Tail

theorem surrogateDiagonalTailChunk000Sub001Block023_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block023HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block023MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block023TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block023Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block023 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block023HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block023MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block023TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block023Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block023_eq_head_add_mid_add_tail

/-- Block 024 covers tail-support indices [5600,5625) and q from 9255 to 9293. -/

def TailChunk000Sub001Block024Part000SupportExplicit : Finset ℕ :=
  ([9255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part000 : ℚ :=
  (345178999475 : ℚ) / 737360144932798464

def SurrogateDiagonalTailChunk000Sub001Block024Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9255
    = surrogateDiagTailX0RatChunk000Sub001Block024Part000

theorem surrogateDiagonalTailChunk000Sub001Block024Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part000] using hcert

def TailChunk000Sub001Block024Part001SupportExplicit : Finset ℕ :=
  ([9257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block024Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9257
    = surrogateDiagTailX0RatChunk000Sub001Block024Part001

theorem surrogateDiagonalTailChunk000Sub001Block024Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part001] using hcert

def TailChunk000Sub001Block024Part002SupportExplicit : Finset ℕ :=
  ([9258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part002 : ℚ :=
  (29742875 : ℚ) / 7538348852928

def SurrogateDiagonalTailChunk000Sub001Block024Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9258
    = surrogateDiagTailX0RatChunk000Sub001Block024Part002

theorem surrogateDiagonalTailChunk000Sub001Block024Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part002] using hcert

def TailChunk000Sub001Block024Part003SupportExplicit : Finset ℕ :=
  ([9259] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part003 : ℚ :=
  (74061884125 : ℚ) / 16522755299085600768

def SurrogateDiagonalTailChunk000Sub001Block024Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9259
    = surrogateDiagTailX0RatChunk000Sub001Block024Part003

theorem surrogateDiagonalTailChunk000Sub001Block024Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part003] using hcert

def TailChunk000Sub001Block024Part004SupportExplicit : Finset ℕ :=
  ([9262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part004 : ℚ :=
  (103049213 : ℚ) / 34581314880000

def SurrogateDiagonalTailChunk000Sub001Block024Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9262
    = surrogateDiagTailX0RatChunk000Sub001Block024Part004

theorem surrogateDiagonalTailChunk000Sub001Block024Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part004] using hcert

def TailChunk000Sub001Block024Part005SupportExplicit : Finset ℕ :=
  ([9263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part005 : ℚ :=
  (2591287265975 : ℚ) / 8379290186208175104

def SurrogateDiagonalTailChunk000Sub001Block024Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9263
    = surrogateDiagTailX0RatChunk000Sub001Block024Part005

theorem surrogateDiagonalTailChunk000Sub001Block024Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part005] using hcert

def TailChunk000Sub001Block024Part006SupportExplicit : Finset ℕ :=
  ([9265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part006 : ℚ :=
  (3498320995375 : ℚ) / 5707445547741216768

def SurrogateDiagonalTailChunk000Sub001Block024Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9265
    = surrogateDiagTailX0RatChunk000Sub001Block024Part006

theorem surrogateDiagonalTailChunk000Sub001Block024Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part006] using hcert

def TailChunk000Sub001Block024Part007SupportExplicit : Finset ℕ :=
  ([9266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part007 : ℚ :=
  (51102136157 : ℚ) / 20145076017561600

def SurrogateDiagonalTailChunk000Sub001Block024Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9266
    = surrogateDiagTailX0RatChunk000Sub001Block024Part007

theorem surrogateDiagonalTailChunk000Sub001Block024Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part007] using hcert

def TailChunk000Sub001Block024Part008SupportExplicit : Finset ℕ :=
  ([9267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part008 : ℚ :=
  (1490510823725 : ℚ) / 1818971994325254144

def SurrogateDiagonalTailChunk000Sub001Block024Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9267
    = surrogateDiagTailX0RatChunk000Sub001Block024Part008

theorem surrogateDiagonalTailChunk000Sub001Block024Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part008] using hcert

def TailChunk000Sub001Block024Part009SupportExplicit : Finset ℕ :=
  ([9269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part009 : ℚ :=
  (17057136871 : ℚ) / 39353881772113920

def SurrogateDiagonalTailChunk000Sub001Block024Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9269
    = surrogateDiagTailX0RatChunk000Sub001Block024Part009

theorem surrogateDiagonalTailChunk000Sub001Block024Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part009] using hcert

def TailChunk000Sub001Block024Part010SupportExplicit : Finset ℕ :=
  ([9271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part010 : ℚ :=
  (5204347070875 : ℚ) / 16937098961948540928

def SurrogateDiagonalTailChunk000Sub001Block024Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9271
    = surrogateDiagTailX0RatChunk000Sub001Block024Part010

theorem surrogateDiagonalTailChunk000Sub001Block024Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part010] using hcert

def TailChunk000Sub001Block024Part011SupportExplicit : Finset ℕ :=
  ([9273] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part011 : ℚ :=
  (10434127183 : ℚ) / 9836462899200000

def SurrogateDiagonalTailChunk000Sub001Block024Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9273
    = surrogateDiagTailX0RatChunk000Sub001Block024Part011

theorem surrogateDiagonalTailChunk000Sub001Block024Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part011] using hcert

def TailChunk000Sub001Block024Part012SupportExplicit : Finset ℕ :=
  ([9274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part012 : ℚ :=
  (335965140625 : ℚ) / 288762356116798752

def SurrogateDiagonalTailChunk000Sub001Block024Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9274
    = surrogateDiagTailX0RatChunk000Sub001Block024Part012

theorem surrogateDiagonalTailChunk000Sub001Block024Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part012] using hcert

def TailChunk000Sub001Block024Part013SupportExplicit : Finset ℕ :=
  ([9277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part013 : ℚ :=
  (1344730140625 : ℚ) / 4628175589727299872

def SurrogateDiagonalTailChunk000Sub001Block024Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9277
    = surrogateDiagTailX0RatChunk000Sub001Block024Part013

theorem surrogateDiagonalTailChunk000Sub001Block024Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part013] using hcert

def TailChunk000Sub001Block024Part014SupportExplicit : Finset ℕ :=
  ([9278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part014 : ℚ :=
  (336255015625 : ℚ) / 289260974357956242

def SurrogateDiagonalTailChunk000Sub001Block024Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9278
    = surrogateDiagTailX0RatChunk000Sub001Block024Part014

theorem surrogateDiagonalTailChunk000Sub001Block024Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part014] using hcert

def TailChunk000Sub001Block024Part015SupportExplicit : Finset ℕ :=
  ([9281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part015 : ℚ :=
  (2153424025 : ℚ) / 7417862094323712

def SurrogateDiagonalTailChunk000Sub001Block024Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9281
    = surrogateDiagTailX0RatChunk000Sub001Block024Part015

theorem surrogateDiagonalTailChunk000Sub001Block024Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part015] using hcert

def TailChunk000Sub001Block024Part016SupportExplicit : Finset ℕ :=
  ([9282] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part016 : ℚ :=
  (339980167775 : ℚ) / 35231145356427264

def SurrogateDiagonalTailChunk000Sub001Block024Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9282
    = surrogateDiagTailX0RatChunk000Sub001Block024Part016

theorem surrogateDiagonalTailChunk000Sub001Block024Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part016] using hcert

def TailChunk000Sub001Block024Part017SupportExplicit : Finset ℕ :=
  ([9283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part017 : ℚ :=
  (1346470140625 : ℚ) / 4640161794111074322

def SurrogateDiagonalTailChunk000Sub001Block024Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9283
    = surrogateDiagTailX0RatChunk000Sub001Block024Part017

theorem surrogateDiagonalTailChunk000Sub001Block024Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part017] using hcert

def TailChunk000Sub001Block024Part018SupportExplicit : Finset ℕ :=
  ([9285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part018 : ℚ :=
  (1063568215625 : ℚ) / 746982988617498624

def SurrogateDiagonalTailChunk000Sub001Block024Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9285
    = surrogateDiagTailX0RatChunk000Sub001Block024Part018

theorem surrogateDiagonalTailChunk000Sub001Block024Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part018] using hcert

def TailChunk000Sub001Block024Part019SupportExplicit : Finset ℕ :=
  ([9286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part019 : ℚ :=
  (336835140625 : ℚ) / 290260147778281362

def SurrogateDiagonalTailChunk000Sub001Block024Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9286
    = surrogateDiagTailX0RatChunk000Sub001Block024Part019

theorem surrogateDiagonalTailChunk000Sub001Block024Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part019] using hcert

def TailChunk000Sub001Block024Part020SupportExplicit : Finset ℕ :=
  ([9287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part020 : ℚ :=
  (1905460171 : ℚ) / 6076215000000000

def SurrogateDiagonalTailChunk000Sub001Block024Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9287
    = surrogateDiagTailX0RatChunk000Sub001Block024Part020

theorem surrogateDiagonalTailChunk000Sub001Block024Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part020] using hcert

def TailChunk000Sub001Block024Part021SupportExplicit : Finset ℕ :=
  ([9289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part021 : ℚ :=
  (238240493375 : ℚ) / 556587503833398336

def SurrogateDiagonalTailChunk000Sub001Block024Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9289
    = surrogateDiagTailX0RatChunk000Sub001Block024Part021

theorem surrogateDiagonalTailChunk000Sub001Block024Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part021] using hcert

def TailChunk000Sub001Block024Part022SupportExplicit : Finset ℕ :=
  ([9290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part022 : ℚ :=
  (538972647875 : ℚ) / 237371587018358784

def SurrogateDiagonalTailChunk000Sub001Block024Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9290
    = surrogateDiagTailX0RatChunk000Sub001Block024Part022

theorem surrogateDiagonalTailChunk000Sub001Block024Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part022] using hcert

def TailChunk000Sub001Block024Part023SupportExplicit : Finset ℕ :=
  ([9291] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part023 : ℚ :=
  (2760638930125 : ℚ) / 2892656869256153088

def SurrogateDiagonalTailChunk000Sub001Block024Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9291
    = surrogateDiagTailX0RatChunk000Sub001Block024Part023

theorem surrogateDiagonalTailChunk000Sub001Block024Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part023] using hcert

def TailChunk000Sub001Block024Part024SupportExplicit : Finset ℕ :=
  ([9293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block024Part024 : ℚ :=
  (1349372640625 : ℚ) / 4660190519932199712

def SurrogateDiagonalTailChunk000Sub001Block024Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9293
    = surrogateDiagTailX0RatChunk000Sub001Block024Part024

theorem surrogateDiagonalTailChunk000Sub001Block024Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block024Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block024Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block024Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block024Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block024Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block024HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block024Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block024Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block024Part000
    + surrogateDiagTailX0RatChunk000Sub001Block024Part001
    + surrogateDiagTailX0RatChunk000Sub001Block024Part002
    + surrogateDiagTailX0RatChunk000Sub001Block024Part003
    + surrogateDiagTailX0RatChunk000Sub001Block024Part004
    + surrogateDiagTailX0RatChunk000Sub001Block024Part005
    + surrogateDiagTailX0RatChunk000Sub001Block024Part006
    + surrogateDiagTailX0RatChunk000Sub001Block024Part007
    + surrogateDiagTailX0RatChunk000Sub001Block024Part008
    + surrogateDiagTailX0RatChunk000Sub001Block024Part009

def surrogateDiagonalTailChunk000Sub001Block024MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block024Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block024Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block024Part010
    + surrogateDiagTailX0RatChunk000Sub001Block024Part011
    + surrogateDiagTailX0RatChunk000Sub001Block024Part012
    + surrogateDiagTailX0RatChunk000Sub001Block024Part013
    + surrogateDiagTailX0RatChunk000Sub001Block024Part014
    + surrogateDiagTailX0RatChunk000Sub001Block024Part015
    + surrogateDiagTailX0RatChunk000Sub001Block024Part016
    + surrogateDiagTailX0RatChunk000Sub001Block024Part017
    + surrogateDiagTailX0RatChunk000Sub001Block024Part018
    + surrogateDiagTailX0RatChunk000Sub001Block024Part019

def surrogateDiagonalTailChunk000Sub001Block024TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block024Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block024Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block024Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block024Part020
    + surrogateDiagTailX0RatChunk000Sub001Block024Part021
    + surrogateDiagTailX0RatChunk000Sub001Block024Part022
    + surrogateDiagTailX0RatChunk000Sub001Block024Part023
    + surrogateDiagTailX0RatChunk000Sub001Block024Part024

def surrogateDiagonalTailChunk000Sub001Block024Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block024HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block024MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block024TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block024 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block024Part000
    + surrogateDiagTailX0RatChunk000Sub001Block024Part001
    + surrogateDiagTailX0RatChunk000Sub001Block024Part002
    + surrogateDiagTailX0RatChunk000Sub001Block024Part003
    + surrogateDiagTailX0RatChunk000Sub001Block024Part004
    + surrogateDiagTailX0RatChunk000Sub001Block024Part005
    + surrogateDiagTailX0RatChunk000Sub001Block024Part006
    + surrogateDiagTailX0RatChunk000Sub001Block024Part007
    + surrogateDiagTailX0RatChunk000Sub001Block024Part008
    + surrogateDiagTailX0RatChunk000Sub001Block024Part009
    + surrogateDiagTailX0RatChunk000Sub001Block024Part010
    + surrogateDiagTailX0RatChunk000Sub001Block024Part011
    + surrogateDiagTailX0RatChunk000Sub001Block024Part012
    + surrogateDiagTailX0RatChunk000Sub001Block024Part013
    + surrogateDiagTailX0RatChunk000Sub001Block024Part014
    + surrogateDiagTailX0RatChunk000Sub001Block024Part015
    + surrogateDiagTailX0RatChunk000Sub001Block024Part016
    + surrogateDiagTailX0RatChunk000Sub001Block024Part017
    + surrogateDiagTailX0RatChunk000Sub001Block024Part018
    + surrogateDiagTailX0RatChunk000Sub001Block024Part019
    + surrogateDiagTailX0RatChunk000Sub001Block024Part020
    + surrogateDiagTailX0RatChunk000Sub001Block024Part021
    + surrogateDiagTailX0RatChunk000Sub001Block024Part022
    + surrogateDiagTailX0RatChunk000Sub001Block024Part023
    + surrogateDiagTailX0RatChunk000Sub001Block024Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block024_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block024Head + surrogateDiagTailX0RatChunk000Sub001Block024Mid + surrogateDiagTailX0RatChunk000Sub001Block024Tail =
      surrogateDiagTailX0RatChunk000Sub001Block024 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block024Head surrogateDiagTailX0RatChunk000Sub001Block024Mid surrogateDiagTailX0RatChunk000Sub001Block024Tail surrogateDiagTailX0RatChunk000Sub001Block024
  ring

def SurrogateDiagonalTailChunk000Sub001Block024HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block024HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block024Head

def SurrogateDiagonalTailChunk000Sub001Block024MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block024MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block024Mid

def SurrogateDiagonalTailChunk000Sub001Block024TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block024TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block024Tail

theorem surrogateDiagonalTailChunk000Sub001Block024_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block024HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block024MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block024TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block024Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block024 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block024HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block024MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block024TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block024Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block024_eq_head_add_mid_add_tail

/-- Block 025 covers tail-support indices [5625,5650) and q from 9294 to 9337. -/

def TailChunk000Sub001Block025Part000SupportExplicit : Finset ℕ :=
  ([9294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part000 : ℚ :=
  (1049187496525 : ℚ) / 229736852599523328

def SurrogateDiagonalTailChunk000Sub001Block025Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9294
    = surrogateDiagTailX0RatChunk000Sub001Block025Part000

theorem surrogateDiagonalTailChunk000Sub001Block025Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part000] using hcert

def TailChunk000Sub001Block025Part001SupportExplicit : Finset ℕ :=
  ([9298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part001 : ℚ :=
  (337706265625 : ℚ) / 291763758609265152

def SurrogateDiagonalTailChunk000Sub001Block025Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9298
    = surrogateDiagTailX0RatChunk000Sub001Block025Part001

theorem surrogateDiagonalTailChunk000Sub001Block025Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part001] using hcert

def TailChunk000Sub001Block025Part002SupportExplicit : Finset ℕ :=
  ([9299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part002 : ℚ :=
  (4924640771125 : ℚ) / 14563889002232414208

def SurrogateDiagonalTailChunk000Sub001Block025Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9299
    = surrogateDiagTailX0RatChunk000Sub001Block025Part002

theorem surrogateDiagonalTailChunk000Sub001Block025Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part002] using hcert

def TailChunk000Sub001Block025Part003SupportExplicit : Finset ℕ :=
  ([9301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part003 : ℚ :=
  (209478145489 : ℚ) / 685886759922000000

def SurrogateDiagonalTailChunk000Sub001Block025Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9301
    = surrogateDiagTailX0RatChunk000Sub001Block025Part003

theorem surrogateDiagonalTailChunk000Sub001Block025Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part003] using hcert

def TailChunk000Sub001Block025Part004SupportExplicit : Finset ℕ :=
  ([9302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part004 : ℚ :=
  (21631801 : ℚ) / 18705040510050

def SurrogateDiagonalTailChunk000Sub001Block025Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9302
    = surrogateDiagTailX0RatChunk000Sub001Block025Part004

theorem surrogateDiagonalTailChunk000Sub001Block025Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part004] using hcert

def TailChunk000Sub001Block025Part005SupportExplicit : Finset ℕ :=
  ([9303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part005 : ℚ :=
  (1957142353975 : ℚ) / 1978977791407638528

def SurrogateDiagonalTailChunk000Sub001Block025Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9303
    = surrogateDiagTailX0RatChunk000Sub001Block025Part005

theorem surrogateDiagonalTailChunk000Sub001Block025Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part005] using hcert

def TailChunk000Sub001Block025Part006SupportExplicit : Finset ℕ :=
  ([9305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part006 : ℚ :=
  (155756229637 : ℚ) / 306463383716659200

def SurrogateDiagonalTailChunk000Sub001Block025Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9305
    = surrogateDiagTailX0RatChunk000Sub001Block025Part006

theorem surrogateDiagonalTailChunk000Sub001Block025Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part006] using hcert

def TailChunk000Sub001Block025Part007SupportExplicit : Finset ℕ :=
  ([9307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part007 : ℚ :=
  (41502766931 : ℚ) / 133595111810826240

def SurrogateDiagonalTailChunk000Sub001Block025Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9307
    = surrogateDiagTailX0RatChunk000Sub001Block025Part007

theorem surrogateDiagonalTailChunk000Sub001Block025Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part007] using hcert

def TailChunk000Sub001Block025Part008SupportExplicit : Finset ℕ :=
  ([9309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part008 : ℚ :=
  (1141678509575 : ℚ) / 1552288472266850304

def SurrogateDiagonalTailChunk000Sub001Block025Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9309
    = surrogateDiagTailX0RatChunk000Sub001Block025Part008

theorem surrogateDiagonalTailChunk000Sub001Block025Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part008] using hcert

def TailChunk000Sub001Block025Part009SupportExplicit : Finset ℕ :=
  ([9311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part009 : ℚ :=
  (2167368025 : ℚ) / 7514248860472242

def SurrogateDiagonalTailChunk000Sub001Block025Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9311
    = surrogateDiagTailX0RatChunk000Sub001Block025Part009

theorem surrogateDiagonalTailChunk000Sub001Block025Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part009] using hcert

def TailChunk000Sub001Block025Part010SupportExplicit : Finset ℕ :=
  ([9313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part010 : ℚ :=
  (43369089175 : ℚ) / 142211126407413888

def SurrogateDiagonalTailChunk000Sub001Block025Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9313
    = surrogateDiagTailX0RatChunk000Sub001Block025Part010

theorem surrogateDiagonalTailChunk000Sub001Block025Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part010] using hcert

def TailChunk000Sub001Block025Part011SupportExplicit : Finset ℕ :=
  ([9314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part011 : ℚ :=
  (338869515625 : ℚ) / 293777651112026112

def SurrogateDiagonalTailChunk000Sub001Block025Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9314
    = surrogateDiagTailX0RatChunk000Sub001Block025Part011

theorem surrogateDiagonalTailChunk000Sub001Block025Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part011] using hcert

def TailChunk000Sub001Block025Part012SupportExplicit : Finset ℕ :=
  ([9318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part012 : ℚ :=
  (1054613426425 : ℚ) / 232120613224316928

def SurrogateDiagonalTailChunk000Sub001Block025Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9318
    = surrogateDiagTailX0RatChunk000Sub001Block025Part012

theorem surrogateDiagonalTailChunk000Sub001Block025Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part012] using hcert

def TailChunk000Sub001Block025Part013SupportExplicit : Finset ℕ :=
  ([9319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part013 : ℚ :=
  (1356933765625 : ℚ) / 4712568673779311922

def SurrogateDiagonalTailChunk000Sub001Block025Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9319
    = surrogateDiagTailX0RatChunk000Sub001Block025Part013

theorem surrogateDiagonalTailChunk000Sub001Block025Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part013] using hcert

def TailChunk000Sub001Block025Part014SupportExplicit : Finset ℕ :=
  ([9321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part014 : ℚ :=
  (191736631175 : ℚ) / 190130424691802112

def SurrogateDiagonalTailChunk000Sub001Block025Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9321
    = surrogateDiagTailX0RatChunk000Sub001Block025Part014

theorem surrogateDiagonalTailChunk000Sub001Block025Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part014] using hcert

def TailChunk000Sub001Block025Part015SupportExplicit : Finset ℕ :=
  ([9322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part015 : ℚ :=
  (1687054475 : ℚ) / 1337690004183936

def SurrogateDiagonalTailChunk000Sub001Block025Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9322
    = surrogateDiagTailX0RatChunk000Sub001Block025Part015

theorem surrogateDiagonalTailChunk000Sub001Block025Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part015] using hcert

def TailChunk000Sub001Block025Part016SupportExplicit : Finset ℕ :=
  ([9323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part016 : ℚ :=
  (1358098890625 : ℚ) / 4720665868947322482

def SurrogateDiagonalTailChunk000Sub001Block025Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9323
    = surrogateDiagTailX0RatChunk000Sub001Block025Part016

theorem surrogateDiagonalTailChunk000Sub001Block025Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part016] using hcert

def TailChunk000Sub001Block025Part017SupportExplicit : Finset ℕ :=
  ([9326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part017 : ℚ :=
  (339743265625 : ℚ) / 295294898577491442

def SurrogateDiagonalTailChunk000Sub001Block025Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9326
    = surrogateDiagTailX0RatChunk000Sub001Block025Part017

theorem surrogateDiagonalTailChunk000Sub001Block025Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part017] using hcert

def TailChunk000Sub001Block025Part018SupportExplicit : Finset ℕ :=
  ([9327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part018 : ℚ :=
  (1509876421475 : ℚ) / 1866555408292291584

def SurrogateDiagonalTailChunk000Sub001Block025Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9327
    = surrogateDiagTailX0RatChunk000Sub001Block025Part018

theorem surrogateDiagonalTailChunk000Sub001Block025Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part018] using hcert

def TailChunk000Sub001Block025Part019SupportExplicit : Finset ℕ :=
  ([9329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part019 : ℚ :=
  (100068766247 : ℚ) / 302643391462977600

def SurrogateDiagonalTailChunk000Sub001Block025Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9329
    = surrogateDiagTailX0RatChunk000Sub001Block025Part019

theorem surrogateDiagonalTailChunk000Sub001Block025Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part019] using hcert

def TailChunk000Sub001Block025Part020SupportExplicit : Finset ℕ :=
  ([9330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part020 : ℚ :=
  (9965495289 : ℚ) / 1261166188134400

def SurrogateDiagonalTailChunk000Sub001Block025Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9330
    = surrogateDiagTailX0RatChunk000Sub001Block025Part020

theorem surrogateDiagonalTailChunk000Sub001Block025Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part020] using hcert

def TailChunk000Sub001Block025Part021SupportExplicit : Finset ℕ :=
  ([9331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part021 : ℚ :=
  (5770916549 : ℚ) / 12100693702809600

def SurrogateDiagonalTailChunk000Sub001Block025Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9331
    = surrogateDiagTailX0RatChunk000Sub001Block025Part021

theorem surrogateDiagonalTailChunk000Sub001Block025Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part021] using hcert

def TailChunk000Sub001Block025Part022SupportExplicit : Finset ℕ :=
  ([9334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part022 : ℚ :=
  (420534520325 : ℚ) / 283898236576536576

def SurrogateDiagonalTailChunk000Sub001Block025Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9334
    = surrogateDiagTailX0RatChunk000Sub001Block025Part022

theorem surrogateDiagonalTailChunk000Sub001Block025Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part022] using hcert

def TailChunk000Sub001Block025Part023SupportExplicit : Finset ℕ :=
  ([9335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part023 : ℚ :=
  (3919060153825 : ℚ) / 7760923129250039808

def SurrogateDiagonalTailChunk000Sub001Block025Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9335
    = surrogateDiagTailX0RatChunk000Sub001Block025Part023

theorem surrogateDiagonalTailChunk000Sub001Block025Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part023] using hcert

def TailChunk000Sub001Block025Part024SupportExplicit : Finset ℕ :=
  ([9337] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block025Part024 : ℚ :=
  (1362180765625 : ℚ) / 4749088247425700352

def SurrogateDiagonalTailChunk000Sub001Block025Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9337
    = surrogateDiagTailX0RatChunk000Sub001Block025Part024

theorem surrogateDiagonalTailChunk000Sub001Block025Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block025Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block025Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block025Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block025Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block025Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block025HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block025Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block025Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block025Part000
    + surrogateDiagTailX0RatChunk000Sub001Block025Part001
    + surrogateDiagTailX0RatChunk000Sub001Block025Part002
    + surrogateDiagTailX0RatChunk000Sub001Block025Part003
    + surrogateDiagTailX0RatChunk000Sub001Block025Part004
    + surrogateDiagTailX0RatChunk000Sub001Block025Part005
    + surrogateDiagTailX0RatChunk000Sub001Block025Part006
    + surrogateDiagTailX0RatChunk000Sub001Block025Part007
    + surrogateDiagTailX0RatChunk000Sub001Block025Part008
    + surrogateDiagTailX0RatChunk000Sub001Block025Part009

def surrogateDiagonalTailChunk000Sub001Block025MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block025Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block025Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block025Part010
    + surrogateDiagTailX0RatChunk000Sub001Block025Part011
    + surrogateDiagTailX0RatChunk000Sub001Block025Part012
    + surrogateDiagTailX0RatChunk000Sub001Block025Part013
    + surrogateDiagTailX0RatChunk000Sub001Block025Part014
    + surrogateDiagTailX0RatChunk000Sub001Block025Part015
    + surrogateDiagTailX0RatChunk000Sub001Block025Part016
    + surrogateDiagTailX0RatChunk000Sub001Block025Part017
    + surrogateDiagTailX0RatChunk000Sub001Block025Part018
    + surrogateDiagTailX0RatChunk000Sub001Block025Part019

def surrogateDiagonalTailChunk000Sub001Block025TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block025Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block025Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block025Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block025Part020
    + surrogateDiagTailX0RatChunk000Sub001Block025Part021
    + surrogateDiagTailX0RatChunk000Sub001Block025Part022
    + surrogateDiagTailX0RatChunk000Sub001Block025Part023
    + surrogateDiagTailX0RatChunk000Sub001Block025Part024

def surrogateDiagonalTailChunk000Sub001Block025Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block025HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block025MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block025TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block025 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block025Part000
    + surrogateDiagTailX0RatChunk000Sub001Block025Part001
    + surrogateDiagTailX0RatChunk000Sub001Block025Part002
    + surrogateDiagTailX0RatChunk000Sub001Block025Part003
    + surrogateDiagTailX0RatChunk000Sub001Block025Part004
    + surrogateDiagTailX0RatChunk000Sub001Block025Part005
    + surrogateDiagTailX0RatChunk000Sub001Block025Part006
    + surrogateDiagTailX0RatChunk000Sub001Block025Part007
    + surrogateDiagTailX0RatChunk000Sub001Block025Part008
    + surrogateDiagTailX0RatChunk000Sub001Block025Part009
    + surrogateDiagTailX0RatChunk000Sub001Block025Part010
    + surrogateDiagTailX0RatChunk000Sub001Block025Part011
    + surrogateDiagTailX0RatChunk000Sub001Block025Part012
    + surrogateDiagTailX0RatChunk000Sub001Block025Part013
    + surrogateDiagTailX0RatChunk000Sub001Block025Part014
    + surrogateDiagTailX0RatChunk000Sub001Block025Part015
    + surrogateDiagTailX0RatChunk000Sub001Block025Part016
    + surrogateDiagTailX0RatChunk000Sub001Block025Part017
    + surrogateDiagTailX0RatChunk000Sub001Block025Part018
    + surrogateDiagTailX0RatChunk000Sub001Block025Part019
    + surrogateDiagTailX0RatChunk000Sub001Block025Part020
    + surrogateDiagTailX0RatChunk000Sub001Block025Part021
    + surrogateDiagTailX0RatChunk000Sub001Block025Part022
    + surrogateDiagTailX0RatChunk000Sub001Block025Part023
    + surrogateDiagTailX0RatChunk000Sub001Block025Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block025_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block025Head + surrogateDiagTailX0RatChunk000Sub001Block025Mid + surrogateDiagTailX0RatChunk000Sub001Block025Tail =
      surrogateDiagTailX0RatChunk000Sub001Block025 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block025Head surrogateDiagTailX0RatChunk000Sub001Block025Mid surrogateDiagTailX0RatChunk000Sub001Block025Tail surrogateDiagTailX0RatChunk000Sub001Block025
  ring

def SurrogateDiagonalTailChunk000Sub001Block025HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block025HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block025Head

def SurrogateDiagonalTailChunk000Sub001Block025MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block025MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block025Mid

def SurrogateDiagonalTailChunk000Sub001Block025TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block025TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block025Tail

theorem surrogateDiagonalTailChunk000Sub001Block025_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block025HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block025MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block025TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block025Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block025 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block025HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block025MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block025TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block025Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block025_eq_head_add_mid_add_tail

/-- Block 026 covers tail-support indices [5650,5675) and q from 9338 to 9379. -/

def TailChunk000Sub001Block026Part000SupportExplicit : Finset ℕ :=
  ([9338] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part000 : ℚ :=
  (69206489425 : ℚ) / 29163169794705408

def SurrogateDiagonalTailChunk000Sub001Block026Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9338
    = surrogateDiagTailX0RatChunk000Sub001Block026Part000

theorem surrogateDiagonalTailChunk000Sub001Block026Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part000] using hcert

def TailChunk000Sub001Block026Part001SupportExplicit : Finset ℕ :=
  ([9339] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part001 : ℚ :=
  (235185805 : ℚ) / 224900671620096

def SurrogateDiagonalTailChunk000Sub001Block026Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9339
    = surrogateDiagTailX0RatChunk000Sub001Block026Part001

theorem surrogateDiagonalTailChunk000Sub001Block026Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part001] using hcert

def TailChunk000Sub001Block026Part002SupportExplicit : Finset ℕ :=
  ([9341] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part002 : ℚ :=
  (2181357025 : ℚ) / 7611571917341472

def SurrogateDiagonalTailChunk000Sub001Block026Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9341
    = surrogateDiagTailX0RatChunk000Sub001Block026Part002

theorem surrogateDiagonalTailChunk000Sub001Block026Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part002] using hcert

def TailChunk000Sub001Block026Part003SupportExplicit : Finset ℕ :=
  ([9343] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part003 : ℚ :=
  (1363932015625 : ℚ) / 4761308474621478162

def SurrogateDiagonalTailChunk000Sub001Block026Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9343
    = surrogateDiagTailX0RatChunk000Sub001Block026Part003

theorem surrogateDiagonalTailChunk000Sub001Block026Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part003] using hcert

def TailChunk000Sub001Block026Part004SupportExplicit : Finset ℕ :=
  ([9345] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part004 : ℚ :=
  (1795756114375 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub001Block026Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9345
    = surrogateDiagTailX0RatChunk000Sub001Block026Part004

theorem surrogateDiagonalTailChunk000Sub001Block026Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part004] using hcert

def TailChunk000Sub001Block026Part005SupportExplicit : Finset ℕ :=
  ([9346] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part005 : ℚ :=
  (2729070201775 : ℚ) / 1191346779904278528

def SurrogateDiagonalTailChunk000Sub001Block026Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9346
    = surrogateDiagTailX0RatChunk000Sub001Block026Part005

theorem surrogateDiagonalTailChunk000Sub001Block026Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part005] using hcert

def TailChunk000Sub001Block026Part006SupportExplicit : Finset ℕ :=
  ([9347] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part006 : ℚ :=
  (4837516780075 : ℚ) / 13780012770283603968

def SurrogateDiagonalTailChunk000Sub001Block026Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9347
    = surrogateDiagTailX0RatChunk000Sub001Block026Part006

theorem surrogateDiagonalTailChunk000Sub001Block026Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part006] using hcert

def TailChunk000Sub001Block026Part007SupportExplicit : Finset ℕ :=
  ([9349] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part007 : ℚ :=
  (1365684390625 : ℚ) / 4773552270231896352

def SurrogateDiagonalTailChunk000Sub001Block026Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9349
    = surrogateDiagTailX0RatChunk000Sub001Block026Part007

theorem surrogateDiagonalTailChunk000Sub001Block026Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part007] using hcert

def TailChunk000Sub001Block026Part008SupportExplicit : Finset ℕ :=
  ([9353] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part008 : ℚ :=
  (25095738875 : ℚ) / 5735848765099026816

def SurrogateDiagonalTailChunk000Sub001Block026Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9353
    = surrogateDiagTailX0RatChunk000Sub001Block026Part008

theorem surrogateDiagonalTailChunk000Sub001Block026Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part008] using hcert

def TailChunk000Sub001Block026Part009SupportExplicit : Finset ℕ :=
  ([9354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part009 : ℚ :=
  (91088625 : ℚ) / 23568383953984

def SurrogateDiagonalTailChunk000Sub001Block026Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9354
    = surrogateDiagTailX0RatChunk000Sub001Block026Part009

theorem surrogateDiagonalTailChunk000Sub001Block026Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part009] using hcert

def TailChunk000Sub001Block026Part010SupportExplicit : Finset ℕ :=
  ([9355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part010 : ℚ :=
  (17531025649 : ℚ) / 313107334961203200

def SurrogateDiagonalTailChunk000Sub001Block026Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9355
    = surrogateDiagTailX0RatChunk000Sub001Block026Part010

theorem surrogateDiagonalTailChunk000Sub001Block026Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part010] using hcert

def TailChunk000Sub001Block026Part011SupportExplicit : Finset ℕ :=
  ([9357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part011 : ℚ :=
  (304122679775 : ℚ) / 1890694188460567104

def SurrogateDiagonalTailChunk000Sub001Block026Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9357
    = surrogateDiagTailX0RatChunk000Sub001Block026Part011

theorem surrogateDiagonalTailChunk000Sub001Block026Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part011] using hcert

def TailChunk000Sub001Block026Part012SupportExplicit : Finset ℕ :=
  ([9358] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part012 : ℚ :=
  (342078765625 : ℚ) / 299369627835586482

def SurrogateDiagonalTailChunk000Sub001Block026Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9358
    = surrogateDiagTailX0RatChunk000Sub001Block026Part012

theorem surrogateDiagonalTailChunk000Sub001Block026Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part012] using hcert

def TailChunk000Sub001Block026Part013SupportExplicit : Finset ℕ :=
  ([9361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part013 : ℚ :=
  (1027122931 : ℚ) / 24596176107571200

def SurrogateDiagonalTailChunk000Sub001Block026Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9361
    = surrogateDiagTailX0RatChunk000Sub001Block026Part013

theorem surrogateDiagonalTailChunk000Sub001Block026Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part013] using hcert

def TailChunk000Sub001Block026Part014SupportExplicit : Finset ℕ :=
  ([9362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part014 : ℚ :=
  (13201884193 : ℚ) / 10253612812500000

def SurrogateDiagonalTailChunk000Sub001Block026Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9362
    = surrogateDiagTailX0RatChunk000Sub001Block026Part014

theorem surrogateDiagonalTailChunk000Sub001Block026Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part014] using hcert

def TailChunk000Sub001Block026Part015SupportExplicit : Finset ℕ :=
  ([9363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part015 : ℚ :=
  (1218050219 : ℚ) / 7582199605493760

def SurrogateDiagonalTailChunk000Sub001Block026Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9363
    = surrogateDiagTailX0RatChunk000Sub001Block026Part015

theorem surrogateDiagonalTailChunk000Sub001Block026Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part015] using hcert

def TailChunk000Sub001Block026Part016SupportExplicit : Finset ℕ :=
  ([9365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part016 : ℚ :=
  (329029625225 : ℚ) / 3930612275487965184

def SurrogateDiagonalTailChunk000Sub001Block026Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9365
    = surrogateDiagTailX0RatChunk000Sub001Block026Part016

theorem surrogateDiagonalTailChunk000Sub001Block026Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part016] using hcert

def TailChunk000Sub001Block026Part017SupportExplicit : Finset ℕ :=
  ([9366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part017 : ℚ :=
  (391596149075 : ℚ) / 62970007526728704

def SurrogateDiagonalTailChunk000Sub001Block026Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9366
    = surrogateDiagTailX0RatChunk000Sub001Block026Part017

theorem surrogateDiagonalTailChunk000Sub001Block026Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part017] using hcert

def TailChunk000Sub001Block026Part018SupportExplicit : Finset ℕ :=
  ([9367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part018 : ℚ :=
  (367893370525 : ℚ) / 10573747500097732608

def SurrogateDiagonalTailChunk000Sub001Block026Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9367
    = surrogateDiagTailX0RatChunk000Sub001Block026Part018

theorem surrogateDiagonalTailChunk000Sub001Block026Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part018] using hcert

def TailChunk000Sub001Block026Part019SupportExplicit : Finset ℕ :=
  ([9370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part019 : ℚ :=
  (548294511875 : ℚ) / 245663267217997824

def SurrogateDiagonalTailChunk000Sub001Block026Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9370
    = surrogateDiagTailX0RatChunk000Sub001Block026Part019

theorem surrogateDiagonalTailChunk000Sub001Block026Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part019] using hcert

def TailChunk000Sub001Block026Part020SupportExplicit : Finset ℕ :=
  ([9371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block026Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9371
    = surrogateDiagTailX0RatChunk000Sub001Block026Part020

theorem surrogateDiagonalTailChunk000Sub001Block026Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part020] using hcert

def TailChunk000Sub001Block026Part021SupportExplicit : Finset ℕ :=
  ([9373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part021 : ℚ :=
  (9135567475 : ℚ) / 113652124307845632

def SurrogateDiagonalTailChunk000Sub001Block026Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9373
    = surrogateDiagTailX0RatChunk000Sub001Block026Part021

theorem surrogateDiagonalTailChunk000Sub001Block026Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part021] using hcert

def TailChunk000Sub001Block026Part022SupportExplicit : Finset ℕ :=
  ([9374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part022 : ℚ :=
  (49337674625 : ℚ) / 39206247597103104

def SurrogateDiagonalTailChunk000Sub001Block026Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9374
    = surrogateDiagTailX0RatChunk000Sub001Block026Part022

theorem surrogateDiagonalTailChunk000Sub001Block026Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part022] using hcert

def TailChunk000Sub001Block026Part023SupportExplicit : Finset ℕ :=
  ([9377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block026Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9377
    = surrogateDiagTailX0RatChunk000Sub001Block026Part023

theorem surrogateDiagonalTailChunk000Sub001Block026Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part023] using hcert

def TailChunk000Sub001Block026Part024SupportExplicit : Finset ℕ :=
  ([9379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block026Part024 : ℚ :=
  (2520525375 : ℚ) / 741213153026834432

def SurrogateDiagonalTailChunk000Sub001Block026Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9379
    = surrogateDiagTailX0RatChunk000Sub001Block026Part024

theorem surrogateDiagonalTailChunk000Sub001Block026Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block026Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block026Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block026Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block026Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block026Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block026HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block026Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block026Part000
    + surrogateDiagTailX0RatChunk000Sub001Block026Part001
    + surrogateDiagTailX0RatChunk000Sub001Block026Part002
    + surrogateDiagTailX0RatChunk000Sub001Block026Part003
    + surrogateDiagTailX0RatChunk000Sub001Block026Part004
    + surrogateDiagTailX0RatChunk000Sub001Block026Part005
    + surrogateDiagTailX0RatChunk000Sub001Block026Part006
    + surrogateDiagTailX0RatChunk000Sub001Block026Part007
    + surrogateDiagTailX0RatChunk000Sub001Block026Part008
    + surrogateDiagTailX0RatChunk000Sub001Block026Part009

def surrogateDiagonalTailChunk000Sub001Block026MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block026Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block026Part010
    + surrogateDiagTailX0RatChunk000Sub001Block026Part011
    + surrogateDiagTailX0RatChunk000Sub001Block026Part012
    + surrogateDiagTailX0RatChunk000Sub001Block026Part013
    + surrogateDiagTailX0RatChunk000Sub001Block026Part014
    + surrogateDiagTailX0RatChunk000Sub001Block026Part015
    + surrogateDiagTailX0RatChunk000Sub001Block026Part016
    + surrogateDiagTailX0RatChunk000Sub001Block026Part017
    + surrogateDiagTailX0RatChunk000Sub001Block026Part018
    + surrogateDiagTailX0RatChunk000Sub001Block026Part019

def surrogateDiagonalTailChunk000Sub001Block026TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block026Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block026Part020
    + surrogateDiagTailX0RatChunk000Sub001Block026Part021
    + surrogateDiagTailX0RatChunk000Sub001Block026Part022
    + surrogateDiagTailX0RatChunk000Sub001Block026Part023
    + surrogateDiagTailX0RatChunk000Sub001Block026Part024

def surrogateDiagonalTailChunk000Sub001Block026Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block026HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block026MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block026TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block026 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block026Part000
    + surrogateDiagTailX0RatChunk000Sub001Block026Part001
    + surrogateDiagTailX0RatChunk000Sub001Block026Part002
    + surrogateDiagTailX0RatChunk000Sub001Block026Part003
    + surrogateDiagTailX0RatChunk000Sub001Block026Part004
    + surrogateDiagTailX0RatChunk000Sub001Block026Part005
    + surrogateDiagTailX0RatChunk000Sub001Block026Part006
    + surrogateDiagTailX0RatChunk000Sub001Block026Part007
    + surrogateDiagTailX0RatChunk000Sub001Block026Part008
    + surrogateDiagTailX0RatChunk000Sub001Block026Part009
    + surrogateDiagTailX0RatChunk000Sub001Block026Part010
    + surrogateDiagTailX0RatChunk000Sub001Block026Part011
    + surrogateDiagTailX0RatChunk000Sub001Block026Part012
    + surrogateDiagTailX0RatChunk000Sub001Block026Part013
    + surrogateDiagTailX0RatChunk000Sub001Block026Part014
    + surrogateDiagTailX0RatChunk000Sub001Block026Part015
    + surrogateDiagTailX0RatChunk000Sub001Block026Part016
    + surrogateDiagTailX0RatChunk000Sub001Block026Part017
    + surrogateDiagTailX0RatChunk000Sub001Block026Part018
    + surrogateDiagTailX0RatChunk000Sub001Block026Part019
    + surrogateDiagTailX0RatChunk000Sub001Block026Part020
    + surrogateDiagTailX0RatChunk000Sub001Block026Part021
    + surrogateDiagTailX0RatChunk000Sub001Block026Part022
    + surrogateDiagTailX0RatChunk000Sub001Block026Part023
    + surrogateDiagTailX0RatChunk000Sub001Block026Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block026_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block026Head + surrogateDiagTailX0RatChunk000Sub001Block026Mid + surrogateDiagTailX0RatChunk000Sub001Block026Tail =
      surrogateDiagTailX0RatChunk000Sub001Block026 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block026Head surrogateDiagTailX0RatChunk000Sub001Block026Mid surrogateDiagTailX0RatChunk000Sub001Block026Tail surrogateDiagTailX0RatChunk000Sub001Block026
  ring

def SurrogateDiagonalTailChunk000Sub001Block026HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block026HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block026Head

def SurrogateDiagonalTailChunk000Sub001Block026MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block026MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block026Mid

def SurrogateDiagonalTailChunk000Sub001Block026TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block026TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block026Tail

theorem surrogateDiagonalTailChunk000Sub001Block026_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block026HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block026MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block026TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block026Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block026 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block026HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block026MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block026TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block026Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block026_eq_head_add_mid_add_tail

/-- Block 027 covers tail-support indices [5675,5700) and q from 9381 to 9419. -/

def TailChunk000Sub001Block027Part000SupportExplicit : Finset ℕ :=
  ([9381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part000 : ℚ :=
  (301260779575 : ℚ) / 827584215921795072

def SurrogateDiagonalTailChunk000Sub001Block027Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9381
    = surrogateDiagTailX0RatChunk000Sub001Block027Part000

theorem surrogateDiagonalTailChunk000Sub001Block027Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part000] using hcert

def TailChunk000Sub001Block027Part001SupportExplicit : Finset ℕ :=
  ([9382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part001 : ℚ :=
  (550137025 : ℚ) / 483925180893042

def SurrogateDiagonalTailChunk000Sub001Block027Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9382
    = surrogateDiagTailX0RatChunk000Sub001Block027Part001

theorem surrogateDiagonalTailChunk000Sub001Block027Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part001] using hcert

def TailChunk000Sub001Block027Part002SupportExplicit : Finset ℕ :=
  ([9383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part002 : ℚ :=
  (1100274529 : ℚ) / 52704200453944320

def SurrogateDiagonalTailChunk000Sub001Block027Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9383
    = surrogateDiagTailX0RatChunk000Sub001Block027Part002

theorem surrogateDiagonalTailChunk000Sub001Block027Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part002] using hcert

def TailChunk000Sub001Block027Part003SupportExplicit : Finset ℕ :=
  ([9385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part003 : ℚ :=
  (47204937425 : ℚ) / 566330725982257152

def SurrogateDiagonalTailChunk000Sub001Block027Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9385
    = surrogateDiagTailX0RatChunk000Sub001Block027Part003

theorem surrogateDiagonalTailChunk000Sub001Block027Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part003] using hcert

def TailChunk000Sub001Block027Part004SupportExplicit : Finset ℕ :=
  ([9389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part004 : ℚ :=
  (52300603 : ℚ) / 10811506893004800

def SurrogateDiagonalTailChunk000Sub001Block027Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9389
    = surrogateDiagTailX0RatChunk000Sub001Block027Part004

theorem surrogateDiagonalTailChunk000Sub001Block027Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part004] using hcert

def TailChunk000Sub001Block027Part005SupportExplicit : Finset ℕ :=
  ([9390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part005 : ℚ :=
  (184700747425 : ℚ) / 24263038737580032

def SurrogateDiagonalTailChunk000Sub001Block027Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9390
    = surrogateDiagTailX0RatChunk000Sub001Block027Part005

theorem surrogateDiagonalTailChunk000Sub001Block027Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part005] using hcert

def TailChunk000Sub001Block027Part006SupportExplicit : Finset ℕ :=
  ([9391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block027Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9391
    = surrogateDiagTailX0RatChunk000Sub001Block027Part006

theorem surrogateDiagonalTailChunk000Sub001Block027Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part006] using hcert

def TailChunk000Sub001Block027Part007SupportExplicit : Finset ℕ :=
  ([9393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part007 : ℚ :=
  (48137286601 : ℚ) / 129625920000000000

def SurrogateDiagonalTailChunk000Sub001Block027Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9393
    = surrogateDiagTailX0RatChunk000Sub001Block027Part007

theorem surrogateDiagonalTailChunk000Sub001Block027Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part007] using hcert

def TailChunk000Sub001Block027Part008SupportExplicit : Finset ℕ :=
  ([9394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part008 : ℚ :=
  (5335941311 : ℚ) / 2099939904000000

def SurrogateDiagonalTailChunk000Sub001Block027Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9394
    = surrogateDiagTailX0RatChunk000Sub001Block027Part008

theorem surrogateDiagonalTailChunk000Sub001Block027Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part008] using hcert

def TailChunk000Sub001Block027Part009SupportExplicit : Finset ℕ :=
  ([9395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part009 : ℚ :=
  (147340963075 : ℚ) / 2654165020075923456

def SurrogateDiagonalTailChunk000Sub001Block027Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9395
    = surrogateDiagTailX0RatChunk000Sub001Block027Part009

theorem surrogateDiagonalTailChunk000Sub001Block027Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part009] using hcert

def TailChunk000Sub001Block027Part010SupportExplicit : Finset ℕ :=
  ([9397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block027Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9397
    = surrogateDiagTailX0RatChunk000Sub001Block027Part010

theorem surrogateDiagonalTailChunk000Sub001Block027Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part010] using hcert

def TailChunk000Sub001Block027Part011SupportExplicit : Finset ℕ :=
  ([9398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part011 : ℚ :=
  (667541722325 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub001Block027Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9398
    = surrogateDiagTailX0RatChunk000Sub001Block027Part011

theorem surrogateDiagonalTailChunk000Sub001Block027Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part011] using hcert

def TailChunk000Sub001Block027Part012SupportExplicit : Finset ℕ :=
  ([9399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part012 : ℚ :=
  (11880264679 : ℚ) / 27524332309708800

def SurrogateDiagonalTailChunk000Sub001Block027Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9399
    = surrogateDiagTailX0RatChunk000Sub001Block027Part012

theorem surrogateDiagonalTailChunk000Sub001Block027Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part012] using hcert

def TailChunk000Sub001Block027Part013SupportExplicit : Finset ℕ :=
  ([9401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part013 : ℚ :=
  (280620738875 : ℚ) / 3930612275487965184

def SurrogateDiagonalTailChunk000Sub001Block027Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9401
    = surrogateDiagTailX0RatChunk000Sub001Block027Part013

theorem surrogateDiagonalTailChunk000Sub001Block027Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part013] using hcert

def TailChunk000Sub001Block027Part014SupportExplicit : Finset ℕ :=
  ([9402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part014 : ℚ :=
  (30675275 : ℚ) / 8018733267648

def SurrogateDiagonalTailChunk000Sub001Block027Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9402
    = surrogateDiagTailX0RatChunk000Sub001Block027Part014

theorem surrogateDiagonalTailChunk000Sub001Block027Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part014] using hcert

def TailChunk000Sub001Block027Part015SupportExplicit : Finset ℕ :=
  ([9403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block027Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9403
    = surrogateDiagTailX0RatChunk000Sub001Block027Part015

theorem surrogateDiagonalTailChunk000Sub001Block027Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part015] using hcert

def TailChunk000Sub001Block027Part016SupportExplicit : Finset ℕ :=
  ([9406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part016 : ℚ :=
  (345597015625 : ℚ) / 305560608845798802

def SurrogateDiagonalTailChunk000Sub001Block027Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9406
    = surrogateDiagTailX0RatChunk000Sub001Block027Part016

theorem surrogateDiagonalTailChunk000Sub001Block027Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part016] using hcert

def TailChunk000Sub001Block027Part017SupportExplicit : Finset ℕ :=
  ([9407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part017 : ℚ :=
  (65718481025 : ℚ) / 8115742122194386944

def SurrogateDiagonalTailChunk000Sub001Block027Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9407
    = surrogateDiagTailX0RatChunk000Sub001Block027Part017

theorem surrogateDiagonalTailChunk000Sub001Block027Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part017] using hcert

def TailChunk000Sub001Block027Part018SupportExplicit : Finset ℕ :=
  ([9410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part018 : ℚ :=
  (4423883599 : ℚ) / 1999117081067520

def SurrogateDiagonalTailChunk000Sub001Block027Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9410
    = surrogateDiagTailX0RatChunk000Sub001Block027Part018

theorem surrogateDiagonalTailChunk000Sub001Block027Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part018] using hcert

def TailChunk000Sub001Block027Part019SupportExplicit : Finset ℕ :=
  ([9411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part019 : ℚ :=
  (21974325325 : ℚ) / 138195221480472576

def SurrogateDiagonalTailChunk000Sub001Block027Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9411
    = surrogateDiagTailX0RatChunk000Sub001Block027Part019

theorem surrogateDiagonalTailChunk000Sub001Block027Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part019] using hcert

def TailChunk000Sub001Block027Part020SupportExplicit : Finset ℕ :=
  ([9413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block027Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9413
    = surrogateDiagTailX0RatChunk000Sub001Block027Part020

theorem surrogateDiagonalTailChunk000Sub001Block027Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part020] using hcert

def TailChunk000Sub001Block027Part021SupportExplicit : Finset ℕ :=
  ([9415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part021 : ℚ :=
  (52074876775 : ℚ) / 267479818102407168

def SurrogateDiagonalTailChunk000Sub001Block027Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9415
    = surrogateDiagTailX0RatChunk000Sub001Block027Part021

theorem surrogateDiagonalTailChunk000Sub001Block027Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part021] using hcert

def TailChunk000Sub001Block027Part022SupportExplicit : Finset ℕ :=
  ([9417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part022 : ℚ :=
  (91562092225 : ℚ) / 477942827850399744

def SurrogateDiagonalTailChunk000Sub001Block027Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9417
    = surrogateDiagTailX0RatChunk000Sub001Block027Part022

theorem surrogateDiagonalTailChunk000Sub001Block027Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part022] using hcert

def TailChunk000Sub001Block027Part023SupportExplicit : Finset ℕ :=
  ([9418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part023 : ℚ :=
  (1304994133375 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub001Block027Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9418
    = surrogateDiagTailX0RatChunk000Sub001Block027Part023

theorem surrogateDiagonalTailChunk000Sub001Block027Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part023] using hcert

def TailChunk000Sub001Block027Part024SupportExplicit : Finset ℕ :=
  ([9419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block027Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block027Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9419
    = surrogateDiagTailX0RatChunk000Sub001Block027Part024

theorem surrogateDiagonalTailChunk000Sub001Block027Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block027Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block027Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block027Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block027Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block027Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block027HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block027Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block027Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block027Part000
    + surrogateDiagTailX0RatChunk000Sub001Block027Part001
    + surrogateDiagTailX0RatChunk000Sub001Block027Part002
    + surrogateDiagTailX0RatChunk000Sub001Block027Part003
    + surrogateDiagTailX0RatChunk000Sub001Block027Part004
    + surrogateDiagTailX0RatChunk000Sub001Block027Part005
    + surrogateDiagTailX0RatChunk000Sub001Block027Part006
    + surrogateDiagTailX0RatChunk000Sub001Block027Part007
    + surrogateDiagTailX0RatChunk000Sub001Block027Part008
    + surrogateDiagTailX0RatChunk000Sub001Block027Part009

def surrogateDiagonalTailChunk000Sub001Block027MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block027Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block027Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block027Part010
    + surrogateDiagTailX0RatChunk000Sub001Block027Part011
    + surrogateDiagTailX0RatChunk000Sub001Block027Part012
    + surrogateDiagTailX0RatChunk000Sub001Block027Part013
    + surrogateDiagTailX0RatChunk000Sub001Block027Part014
    + surrogateDiagTailX0RatChunk000Sub001Block027Part015
    + surrogateDiagTailX0RatChunk000Sub001Block027Part016
    + surrogateDiagTailX0RatChunk000Sub001Block027Part017
    + surrogateDiagTailX0RatChunk000Sub001Block027Part018
    + surrogateDiagTailX0RatChunk000Sub001Block027Part019

def surrogateDiagonalTailChunk000Sub001Block027TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block027Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block027Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block027Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block027Part020
    + surrogateDiagTailX0RatChunk000Sub001Block027Part021
    + surrogateDiagTailX0RatChunk000Sub001Block027Part022
    + surrogateDiagTailX0RatChunk000Sub001Block027Part023
    + surrogateDiagTailX0RatChunk000Sub001Block027Part024

def surrogateDiagonalTailChunk000Sub001Block027Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block027HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block027MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block027TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block027 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block027Part000
    + surrogateDiagTailX0RatChunk000Sub001Block027Part001
    + surrogateDiagTailX0RatChunk000Sub001Block027Part002
    + surrogateDiagTailX0RatChunk000Sub001Block027Part003
    + surrogateDiagTailX0RatChunk000Sub001Block027Part004
    + surrogateDiagTailX0RatChunk000Sub001Block027Part005
    + surrogateDiagTailX0RatChunk000Sub001Block027Part006
    + surrogateDiagTailX0RatChunk000Sub001Block027Part007
    + surrogateDiagTailX0RatChunk000Sub001Block027Part008
    + surrogateDiagTailX0RatChunk000Sub001Block027Part009
    + surrogateDiagTailX0RatChunk000Sub001Block027Part010
    + surrogateDiagTailX0RatChunk000Sub001Block027Part011
    + surrogateDiagTailX0RatChunk000Sub001Block027Part012
    + surrogateDiagTailX0RatChunk000Sub001Block027Part013
    + surrogateDiagTailX0RatChunk000Sub001Block027Part014
    + surrogateDiagTailX0RatChunk000Sub001Block027Part015
    + surrogateDiagTailX0RatChunk000Sub001Block027Part016
    + surrogateDiagTailX0RatChunk000Sub001Block027Part017
    + surrogateDiagTailX0RatChunk000Sub001Block027Part018
    + surrogateDiagTailX0RatChunk000Sub001Block027Part019
    + surrogateDiagTailX0RatChunk000Sub001Block027Part020
    + surrogateDiagTailX0RatChunk000Sub001Block027Part021
    + surrogateDiagTailX0RatChunk000Sub001Block027Part022
    + surrogateDiagTailX0RatChunk000Sub001Block027Part023
    + surrogateDiagTailX0RatChunk000Sub001Block027Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block027_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block027Head + surrogateDiagTailX0RatChunk000Sub001Block027Mid + surrogateDiagTailX0RatChunk000Sub001Block027Tail =
      surrogateDiagTailX0RatChunk000Sub001Block027 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block027Head surrogateDiagTailX0RatChunk000Sub001Block027Mid surrogateDiagTailX0RatChunk000Sub001Block027Tail surrogateDiagTailX0RatChunk000Sub001Block027
  ring

def SurrogateDiagonalTailChunk000Sub001Block027HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block027HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block027Head

def SurrogateDiagonalTailChunk000Sub001Block027MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block027MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block027Mid

def SurrogateDiagonalTailChunk000Sub001Block027TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block027TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block027Tail

theorem surrogateDiagonalTailChunk000Sub001Block027_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block027HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block027MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block027TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block027Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block027 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block027HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block027MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block027TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block027Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block027_eq_head_add_mid_add_tail

/-- Block 028 covers tail-support indices [5700,5725) and q from 9421 to 9462. -/

def TailChunk000Sub001Block028Part000SupportExplicit : Finset ℕ :=
  ([9421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block028Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9421
    = surrogateDiagTailX0RatChunk000Sub001Block028Part000

theorem surrogateDiagonalTailChunk000Sub001Block028Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part000] using hcert

def TailChunk000Sub001Block028Part001SupportExplicit : Finset ℕ :=
  ([9422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part001 : ℚ :=
  (303935309875 : ℚ) / 165214804689027072

def SurrogateDiagonalTailChunk000Sub001Block028Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9422
    = surrogateDiagTailX0RatChunk000Sub001Block028Part001

theorem surrogateDiagonalTailChunk000Sub001Block028Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part001] using hcert

def TailChunk000Sub001Block028Part002SupportExplicit : Finset ℕ :=
  ([9426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part002 : ℚ :=
  (3699849 : ℚ) / 972117121600

def SurrogateDiagonalTailChunk000Sub001Block028Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9426
    = surrogateDiagTailX0RatChunk000Sub001Block028Part002

theorem surrogateDiagonalTailChunk000Sub001Block028Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part002] using hcert

def TailChunk000Sub001Block028Part003SupportExplicit : Finset ℕ :=
  ([9427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part003 : ℚ :=
  (1110512257 : ℚ) / 53700942610513920

def SurrogateDiagonalTailChunk000Sub001Block028Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9427
    = surrogateDiagTailX0RatChunk000Sub001Block028Part003

theorem surrogateDiagonalTailChunk000Sub001Block028Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part003] using hcert

def TailChunk000Sub001Block028Part004SupportExplicit : Finset ℕ :=
  ([9429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part004 : ℚ :=
  (693741170275 : ℚ) / 2088641481500786688

def SurrogateDiagonalTailChunk000Sub001Block028Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9429
    = surrogateDiagTailX0RatChunk000Sub001Block028Part004

theorem surrogateDiagonalTailChunk000Sub001Block028Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part004] using hcert

def TailChunk000Sub001Block028Part005SupportExplicit : Finset ℕ :=
  ([9430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part005 : ℚ :=
  (2603749543 : ℚ) / 959704478515200

def SurrogateDiagonalTailChunk000Sub001Block028Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9430
    = surrogateDiagTailX0RatChunk000Sub001Block028Part005

theorem surrogateDiagonalTailChunk000Sub001Block028Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part005] using hcert

def TailChunk000Sub001Block028Part006SupportExplicit : Finset ℕ :=
  ([9431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block028Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9431
    = surrogateDiagTailX0RatChunk000Sub001Block028Part006

theorem surrogateDiagonalTailChunk000Sub001Block028Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part006] using hcert

def TailChunk000Sub001Block028Part007SupportExplicit : Finset ℕ :=
  ([9433] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block028Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9433
    = surrogateDiagTailX0RatChunk000Sub001Block028Part007

theorem surrogateDiagonalTailChunk000Sub001Block028Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part007] using hcert

def TailChunk000Sub001Block028Part008SupportExplicit : Finset ℕ :=
  ([9434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part008 : ℚ :=
  (2660410173325 : ℚ) / 1096404784434905088

def SurrogateDiagonalTailChunk000Sub001Block028Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9434
    = surrogateDiagTailX0RatChunk000Sub001Block028Part008

theorem surrogateDiagonalTailChunk000Sub001Block028Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part008] using hcert

def TailChunk000Sub001Block028Part009SupportExplicit : Finset ℕ :=
  ([9435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part009 : ℚ :=
  (9383602325 : ℚ) / 5219428941692928

def SurrogateDiagonalTailChunk000Sub001Block028Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9435
    = surrogateDiagTailX0RatChunk000Sub001Block028Part009

theorem surrogateDiagonalTailChunk000Sub001Block028Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part009] using hcert

def TailChunk000Sub001Block028Part010SupportExplicit : Finset ℕ :=
  ([9437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part010 : ℚ :=
  (1391515140625 : ℚ) / 4955855059883173152

def SurrogateDiagonalTailChunk000Sub001Block028Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9437
    = surrogateDiagTailX0RatChunk000Sub001Block028Part010

theorem surrogateDiagonalTailChunk000Sub001Block028Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part010] using hcert

def TailChunk000Sub001Block028Part011SupportExplicit : Finset ℕ :=
  ([9439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part011 : ℚ :=
  (1392105015625 : ℚ) / 4960058053443249042

def SurrogateDiagonalTailChunk000Sub001Block028Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9439
    = surrogateDiagTailX0RatChunk000Sub001Block028Part011

theorem surrogateDiagonalTailChunk000Sub001Block028Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part011] using hcert

def TailChunk000Sub001Block028Part012SupportExplicit : Finset ℕ :=
  ([9442] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part012 : ℚ :=
  (557196025 : ℚ) / 496426371981312

def SurrogateDiagonalTailChunk000Sub001Block028Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9442
    = surrogateDiagTailX0RatChunk000Sub001Block028Part012

theorem surrogateDiagonalTailChunk000Sub001Block028Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part012] using hcert

def TailChunk000Sub001Block028Part013SupportExplicit : Finset ℕ :=
  ([9443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part013 : ℚ :=
  (11484459611 : ℚ) / 23337052141132800

def SurrogateDiagonalTailChunk000Sub001Block028Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9443
    = surrogateDiagTailX0RatChunk000Sub001Block028Part013

theorem surrogateDiagonalTailChunk000Sub001Block028Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part013] using hcert

def TailChunk000Sub001Block028Part014SupportExplicit : Finset ℕ :=
  ([9445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part014 : ℚ :=
  (1337328702975 : ℚ) / 2711149892847271936

def SurrogateDiagonalTailChunk000Sub001Block028Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9445
    = surrogateDiagTailX0RatChunk000Sub001Block028Part014

theorem surrogateDiagonalTailChunk000Sub001Block028Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part014] using hcert

def TailChunk000Sub001Block028Part015SupportExplicit : Finset ℕ :=
  ([9446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part015 : ℚ :=
  (348542640625 : ℚ) / 310792692219632082

def SurrogateDiagonalTailChunk000Sub001Block028Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9446
    = surrogateDiagTailX0RatChunk000Sub001Block028Part015

theorem surrogateDiagonalTailChunk000Sub001Block028Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part015] using hcert

def TailChunk000Sub001Block028Part016SupportExplicit : Finset ℕ :=
  ([9447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part016 : ℚ :=
  (2948189490325 : ℚ) / 3399021490429052928

def SurrogateDiagonalTailChunk000Sub001Block028Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9447
    = surrogateDiagTailX0RatChunk000Sub001Block028Part016

theorem surrogateDiagonalTailChunk000Sub001Block028Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part016] using hcert

def TailChunk000Sub001Block028Part017SupportExplicit : Finset ℕ :=
  ([9449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part017 : ℚ :=
  (191552539249 : ℚ) / 542045822382979200

def SurrogateDiagonalTailChunk000Sub001Block028Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9449
    = surrogateDiagTailX0RatChunk000Sub001Block028Part017

theorem surrogateDiagonalTailChunk000Sub001Block028Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part017] using hcert

def TailChunk000Sub001Block028Part018SupportExplicit : Finset ℕ :=
  ([9451] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part018 : ℚ :=
  (4945833239275 : ℚ) / 14404504575637997568

def SurrogateDiagonalTailChunk000Sub001Block028Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9451
    = surrogateDiagTailX0RatChunk000Sub001Block028Part018

theorem surrogateDiagonalTailChunk000Sub001Block028Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part018] using hcert

def TailChunk000Sub001Block028Part019SupportExplicit : Finset ℕ :=
  ([9453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part019 : ℚ :=
  (1445054856125 : ℚ) / 1603109555001360384

def SurrogateDiagonalTailChunk000Sub001Block028Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9453
    = surrogateDiagTailX0RatChunk000Sub001Block028Part019

theorem surrogateDiagonalTailChunk000Sub001Block028Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part019] using hcert

def TailChunk000Sub001Block028Part020SupportExplicit : Finset ℕ :=
  ([9454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part020 : ℚ :=
  (192015711625 : ℚ) / 151224097874540544

def SurrogateDiagonalTailChunk000Sub001Block028Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9454
    = surrogateDiagTailX0RatChunk000Sub001Block028Part020

theorem surrogateDiagonalTailChunk000Sub001Block028Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part020] using hcert

def TailChunk000Sub001Block028Part021SupportExplicit : Finset ℕ :=
  ([9455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part021 : ℚ :=
  (300083969 : ℚ) / 537584615424000

def SurrogateDiagonalTailChunk000Sub001Block028Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9455
    = surrogateDiagTailX0RatChunk000Sub001Block028Part021

theorem surrogateDiagonalTailChunk000Sub001Block028Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part021] using hcert

def TailChunk000Sub001Block028Part022SupportExplicit : Finset ℕ :=
  ([9458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part022 : ℚ :=
  (349428765625 : ℚ) / 312375337995244032

def SurrogateDiagonalTailChunk000Sub001Block028Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9458
    = surrogateDiagTailX0RatChunk000Sub001Block028Part022

theorem surrogateDiagonalTailChunk000Sub001Block028Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part022] using hcert

def TailChunk000Sub001Block028Part023SupportExplicit : Finset ℕ :=
  ([9461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part023 : ℚ :=
  (2237763025 : ℚ) / 8010348219854112

def SurrogateDiagonalTailChunk000Sub001Block028Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9461
    = surrogateDiagTailX0RatChunk000Sub001Block028Part023

theorem surrogateDiagonalTailChunk000Sub001Block028Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part023] using hcert

def TailChunk000Sub001Block028Part024SupportExplicit : Finset ℕ :=
  ([9462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block028Part024 : ℚ :=
  (438092504975 : ℚ) / 94942852529071104

def SurrogateDiagonalTailChunk000Sub001Block028Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9462
    = surrogateDiagTailX0RatChunk000Sub001Block028Part024

theorem surrogateDiagonalTailChunk000Sub001Block028Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block028Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block028Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block028Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block028Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block028Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block028HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block028Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block028Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block028Part000
    + surrogateDiagTailX0RatChunk000Sub001Block028Part001
    + surrogateDiagTailX0RatChunk000Sub001Block028Part002
    + surrogateDiagTailX0RatChunk000Sub001Block028Part003
    + surrogateDiagTailX0RatChunk000Sub001Block028Part004
    + surrogateDiagTailX0RatChunk000Sub001Block028Part005
    + surrogateDiagTailX0RatChunk000Sub001Block028Part006
    + surrogateDiagTailX0RatChunk000Sub001Block028Part007
    + surrogateDiagTailX0RatChunk000Sub001Block028Part008
    + surrogateDiagTailX0RatChunk000Sub001Block028Part009

def surrogateDiagonalTailChunk000Sub001Block028MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block028Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block028Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block028Part010
    + surrogateDiagTailX0RatChunk000Sub001Block028Part011
    + surrogateDiagTailX0RatChunk000Sub001Block028Part012
    + surrogateDiagTailX0RatChunk000Sub001Block028Part013
    + surrogateDiagTailX0RatChunk000Sub001Block028Part014
    + surrogateDiagTailX0RatChunk000Sub001Block028Part015
    + surrogateDiagTailX0RatChunk000Sub001Block028Part016
    + surrogateDiagTailX0RatChunk000Sub001Block028Part017
    + surrogateDiagTailX0RatChunk000Sub001Block028Part018
    + surrogateDiagTailX0RatChunk000Sub001Block028Part019

def surrogateDiagonalTailChunk000Sub001Block028TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block028Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block028Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block028Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block028Part020
    + surrogateDiagTailX0RatChunk000Sub001Block028Part021
    + surrogateDiagTailX0RatChunk000Sub001Block028Part022
    + surrogateDiagTailX0RatChunk000Sub001Block028Part023
    + surrogateDiagTailX0RatChunk000Sub001Block028Part024

def surrogateDiagonalTailChunk000Sub001Block028Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block028HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block028MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block028TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block028 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block028Part000
    + surrogateDiagTailX0RatChunk000Sub001Block028Part001
    + surrogateDiagTailX0RatChunk000Sub001Block028Part002
    + surrogateDiagTailX0RatChunk000Sub001Block028Part003
    + surrogateDiagTailX0RatChunk000Sub001Block028Part004
    + surrogateDiagTailX0RatChunk000Sub001Block028Part005
    + surrogateDiagTailX0RatChunk000Sub001Block028Part006
    + surrogateDiagTailX0RatChunk000Sub001Block028Part007
    + surrogateDiagTailX0RatChunk000Sub001Block028Part008
    + surrogateDiagTailX0RatChunk000Sub001Block028Part009
    + surrogateDiagTailX0RatChunk000Sub001Block028Part010
    + surrogateDiagTailX0RatChunk000Sub001Block028Part011
    + surrogateDiagTailX0RatChunk000Sub001Block028Part012
    + surrogateDiagTailX0RatChunk000Sub001Block028Part013
    + surrogateDiagTailX0RatChunk000Sub001Block028Part014
    + surrogateDiagTailX0RatChunk000Sub001Block028Part015
    + surrogateDiagTailX0RatChunk000Sub001Block028Part016
    + surrogateDiagTailX0RatChunk000Sub001Block028Part017
    + surrogateDiagTailX0RatChunk000Sub001Block028Part018
    + surrogateDiagTailX0RatChunk000Sub001Block028Part019
    + surrogateDiagTailX0RatChunk000Sub001Block028Part020
    + surrogateDiagTailX0RatChunk000Sub001Block028Part021
    + surrogateDiagTailX0RatChunk000Sub001Block028Part022
    + surrogateDiagTailX0RatChunk000Sub001Block028Part023
    + surrogateDiagTailX0RatChunk000Sub001Block028Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block028_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block028Head + surrogateDiagTailX0RatChunk000Sub001Block028Mid + surrogateDiagTailX0RatChunk000Sub001Block028Tail =
      surrogateDiagTailX0RatChunk000Sub001Block028 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block028Head surrogateDiagTailX0RatChunk000Sub001Block028Mid surrogateDiagTailX0RatChunk000Sub001Block028Tail surrogateDiagTailX0RatChunk000Sub001Block028
  ring

def SurrogateDiagonalTailChunk000Sub001Block028HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block028HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block028Head

def SurrogateDiagonalTailChunk000Sub001Block028MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block028MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block028Mid

def SurrogateDiagonalTailChunk000Sub001Block028TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block028TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block028Tail

theorem surrogateDiagonalTailChunk000Sub001Block028_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block028HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block028MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block028TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block028Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block028 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block028HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block028MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block028TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block028Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block028_eq_head_add_mid_add_tail

/-- Block 029 covers tail-support indices [5725,5750) and q from 9463 to 9501. -/

def TailChunk000Sub001Block029Part000SupportExplicit : Finset ℕ :=
  ([9463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part000 : ℚ :=
  (1399193265625 : ℚ) / 5010702779511078642

def SurrogateDiagonalTailChunk000Sub001Block029Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9463
    = surrogateDiagTailX0RatChunk000Sub001Block029Part000

theorem surrogateDiagonalTailChunk000Sub001Block029Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part000] using hcert

def TailChunk000Sub001Block029Part001SupportExplicit : Finset ℕ :=
  ([9465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part001 : ℚ :=
  (44208957671 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub001Block029Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9465
    = surrogateDiagTailX0RatChunk000Sub001Block029Part001

theorem surrogateDiagonalTailChunk000Sub001Block029Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part001] using hcert

def TailChunk000Sub001Block029Part002SupportExplicit : Finset ℕ :=
  ([9466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part002 : ℚ :=
  (350020140625 : ℚ) / 313433788002115872

def SurrogateDiagonalTailChunk000Sub001Block029Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9466
    = surrogateDiagTailX0RatChunk000Sub001Block029Part002

theorem surrogateDiagonalTailChunk000Sub001Block029Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part002] using hcert

def TailChunk000Sub001Block029Part003SupportExplicit : Finset ℕ :=
  ([9467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part003 : ℚ :=
  (1400376390625 : ℚ) / 5019181124112933042

def SurrogateDiagonalTailChunk000Sub001Block029Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9467
    = surrogateDiagTailX0RatChunk000Sub001Block029Part003

theorem surrogateDiagonalTailChunk000Sub001Block029Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part003] using hcert

def TailChunk000Sub001Block029Part004SupportExplicit : Finset ℕ :=
  ([9469] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part004 : ℚ :=
  (5106498299125 : ℚ) / 15660511970803580928

def SurrogateDiagonalTailChunk000Sub001Block029Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9469
    = surrogateDiagTailX0RatChunk000Sub001Block029Part004

theorem surrogateDiagonalTailChunk000Sub001Block029Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part004] using hcert

def TailChunk000Sub001Block029Part005SupportExplicit : Finset ℕ :=
  ([9470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part005 : ℚ :=
  (392016932625 : ℚ) / 170887428690221056

def SurrogateDiagonalTailChunk000Sub001Block029Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9470
    = surrogateDiagTailX0RatChunk000Sub001Block029Part005

theorem surrogateDiagonalTailChunk000Sub001Block029Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part005] using hcert

def TailChunk000Sub001Block029Part006SupportExplicit : Finset ℕ :=
  ([9471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part006 : ℚ :=
  (71881849849 : ℚ) / 53094776832000000

def SurrogateDiagonalTailChunk000Sub001Block029Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9471
    = surrogateDiagTailX0RatChunk000Sub001Block029Part006

theorem surrogateDiagonalTailChunk000Sub001Block029Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part006] using hcert

def TailChunk000Sub001Block029Part007SupportExplicit : Finset ℕ :=
  ([9473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part007 : ℚ :=
  (1402152015625 : ℚ) / 5031918809049464832

def SurrogateDiagonalTailChunk000Sub001Block029Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9473
    = surrogateDiagTailX0RatChunk000Sub001Block029Part007

theorem surrogateDiagonalTailChunk000Sub001Block029Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part007] using hcert

def TailChunk000Sub001Block029Part008SupportExplicit : Finset ℕ :=
  ([9474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part008 : ℚ :=
  (31146875 : ℚ) / 8267357769408

def SurrogateDiagonalTailChunk000Sub001Block029Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9474
    = surrogateDiagTailX0RatChunk000Sub001Block029Part008

theorem surrogateDiagonalTailChunk000Sub001Block029Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part008] using hcert

def TailChunk000Sub001Block029Part009SupportExplicit : Finset ℕ :=
  ([9478] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part009 : ℚ :=
  (66759672175 : ℚ) / 37596389398004736

def SurrogateDiagonalTailChunk000Sub001Block029Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9478
    = surrogateDiagTailX0RatChunk000Sub001Block029Part009

theorem surrogateDiagonalTailChunk000Sub001Block029Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part009] using hcert

def TailChunk000Sub001Block029Part010SupportExplicit : Finset ℕ :=
  ([9479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part010 : ℚ :=
  (1403928765625 : ℚ) / 5044680722904111282

def SurrogateDiagonalTailChunk000Sub001Block029Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9479
    = surrogateDiagTailX0RatChunk000Sub001Block029Part010

theorem surrogateDiagonalTailChunk000Sub001Block029Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part010] using hcert

def TailChunk000Sub001Block029Part011SupportExplicit : Finset ℕ :=
  ([9481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part011 : ℚ :=
  (2583982593275 : ℚ) / 8072429385624035904

def SurrogateDiagonalTailChunk000Sub001Block029Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9481
    = surrogateDiagTailX0RatChunk000Sub001Block029Part011

theorem surrogateDiagonalTailChunk000Sub001Block029Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part011] using hcert

def TailChunk000Sub001Block029Part012SupportExplicit : Finset ℕ :=
  ([9482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part012 : ℚ :=
  (2549126723 : ℚ) / 1709742380100000

def SurrogateDiagonalTailChunk000Sub001Block029Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9482
    = surrogateDiagTailX0RatChunk000Sub001Block029Part012

theorem surrogateDiagonalTailChunk000Sub001Block029Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part012] using hcert

def TailChunk000Sub001Block029Part013SupportExplicit : Finset ℕ :=
  ([9483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part013 : ℚ :=
  (1183363980125 : ℚ) / 1672799897476399104

def SurrogateDiagonalTailChunk000Sub001Block029Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9483
    = surrogateDiagTailX0RatChunk000Sub001Block029Part013

theorem surrogateDiagonalTailChunk000Sub001Block029Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part013] using hcert

def TailChunk000Sub001Block029Part014SupportExplicit : Finset ℕ :=
  ([9485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part014 : ℚ :=
  (7913277571 : ℚ) / 11022164568115200

def SurrogateDiagonalTailChunk000Sub001Block029Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9485
    = surrogateDiagTailX0RatChunk000Sub001Block029Part014

theorem surrogateDiagonalTailChunk000Sub001Block029Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part014] using hcert

def TailChunk000Sub001Block029Part015SupportExplicit : Finset ℕ :=
  ([9487] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part015 : ℚ :=
  (5425092007225 : ℚ) / 18353556904243611648

def SurrogateDiagonalTailChunk000Sub001Block029Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9487
    = surrogateDiagTailX0RatChunk000Sub001Block029Part015

theorem surrogateDiagonalTailChunk000Sub001Block029Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part015] using hcert

def TailChunk000Sub001Block029Part016SupportExplicit : Finset ℕ :=
  ([9489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part016 : ℚ :=
  (2500185683725 : ℚ) / 3999395042406108288

def SurrogateDiagonalTailChunk000Sub001Block029Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9489
    = surrogateDiagTailX0RatChunk000Sub001Block029Part016

theorem surrogateDiagonalTailChunk000Sub001Block029Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part016] using hcert

def TailChunk000Sub001Block029Part017SupportExplicit : Finset ℕ :=
  ([9490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part017 : ℚ :=
  (1078054379725 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub001Block029Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9490
    = surrogateDiagTailX0RatChunk000Sub001Block029Part017

theorem surrogateDiagonalTailChunk000Sub001Block029Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part017] using hcert

def TailChunk000Sub001Block029Part018SupportExplicit : Finset ℕ :=
  ([9491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part018 : ℚ :=
  (2251977025 : ℚ) / 8112443776332402

def SurrogateDiagonalTailChunk000Sub001Block029Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9491
    = surrogateDiagTailX0RatChunk000Sub001Block029Part018

theorem surrogateDiagonalTailChunk000Sub001Block029Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part018] using hcert

def TailChunk000Sub001Block029Part019SupportExplicit : Finset ℕ :=
  ([9493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part019 : ℚ :=
  (1626697041 : ℚ) / 4601873406776560

def SurrogateDiagonalTailChunk000Sub001Block029Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9493
    = surrogateDiagTailX0RatChunk000Sub001Block029Part019

theorem surrogateDiagonalTailChunk000Sub001Block029Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part019] using hcert

def TailChunk000Sub001Block029Part020SupportExplicit : Finset ℕ :=
  ([9494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part020 : ℚ :=
  (10940692637 : ℚ) / 8956702982400000

def SurrogateDiagonalTailChunk000Sub001Block029Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9494
    = surrogateDiagTailX0RatChunk000Sub001Block029Part020

theorem surrogateDiagonalTailChunk000Sub001Block029Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part020] using hcert

def TailChunk000Sub001Block029Part021SupportExplicit : Finset ℕ :=
  ([9497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part021 : ℚ :=
  (1409265765625 : ℚ) / 5083112145125356032

def SurrogateDiagonalTailChunk000Sub001Block029Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9497
    = surrogateDiagTailX0RatChunk000Sub001Block029Part021

theorem surrogateDiagonalTailChunk000Sub001Block029Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part021] using hcert

def TailChunk000Sub001Block029Part022SupportExplicit : Finset ℕ :=
  ([9498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part022 : ℚ :=
  (1095754227175 : ℚ) / 250595205826401408

def SurrogateDiagonalTailChunk000Sub001Block029Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9498
    = surrogateDiagTailX0RatChunk000Sub001Block029Part022

theorem surrogateDiagonalTailChunk000Sub001Block029Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part022] using hcert

def TailChunk000Sub001Block029Part023SupportExplicit : Finset ℕ :=
  ([9499] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part023 : ℚ :=
  (4107233610925 : ℚ) / 8590818781994600448

def SurrogateDiagonalTailChunk000Sub001Block029Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9499
    = surrogateDiagTailX0RatChunk000Sub001Block029Part023

theorem surrogateDiagonalTailChunk000Sub001Block029Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part023] using hcert

def TailChunk000Sub001Block029Part024SupportExplicit : Finset ℕ :=
  ([9501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block029Part024 : ℚ :=
  (783371821525 : ℚ) / 1004917692201130272

def SurrogateDiagonalTailChunk000Sub001Block029Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 9501
    = surrogateDiagTailX0RatChunk000Sub001Block029Part024

theorem surrogateDiagonalTailChunk000Sub001Block029Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block029Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block029Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block029Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block029Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block029Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block029HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block029Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block029Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block029Part000
    + surrogateDiagTailX0RatChunk000Sub001Block029Part001
    + surrogateDiagTailX0RatChunk000Sub001Block029Part002
    + surrogateDiagTailX0RatChunk000Sub001Block029Part003
    + surrogateDiagTailX0RatChunk000Sub001Block029Part004
    + surrogateDiagTailX0RatChunk000Sub001Block029Part005
    + surrogateDiagTailX0RatChunk000Sub001Block029Part006
    + surrogateDiagTailX0RatChunk000Sub001Block029Part007
    + surrogateDiagTailX0RatChunk000Sub001Block029Part008
    + surrogateDiagTailX0RatChunk000Sub001Block029Part009

def surrogateDiagonalTailChunk000Sub001Block029MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block029Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block029Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block029Part010
    + surrogateDiagTailX0RatChunk000Sub001Block029Part011
    + surrogateDiagTailX0RatChunk000Sub001Block029Part012
    + surrogateDiagTailX0RatChunk000Sub001Block029Part013
    + surrogateDiagTailX0RatChunk000Sub001Block029Part014
    + surrogateDiagTailX0RatChunk000Sub001Block029Part015
    + surrogateDiagTailX0RatChunk000Sub001Block029Part016
    + surrogateDiagTailX0RatChunk000Sub001Block029Part017
    + surrogateDiagTailX0RatChunk000Sub001Block029Part018
    + surrogateDiagTailX0RatChunk000Sub001Block029Part019

def surrogateDiagonalTailChunk000Sub001Block029TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block029Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block029Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block029Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block029Part020
    + surrogateDiagTailX0RatChunk000Sub001Block029Part021
    + surrogateDiagTailX0RatChunk000Sub001Block029Part022
    + surrogateDiagTailX0RatChunk000Sub001Block029Part023
    + surrogateDiagTailX0RatChunk000Sub001Block029Part024

def surrogateDiagonalTailChunk000Sub001Block029Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block029HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block029MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block029TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block029 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block029Part000
    + surrogateDiagTailX0RatChunk000Sub001Block029Part001
    + surrogateDiagTailX0RatChunk000Sub001Block029Part002
    + surrogateDiagTailX0RatChunk000Sub001Block029Part003
    + surrogateDiagTailX0RatChunk000Sub001Block029Part004
    + surrogateDiagTailX0RatChunk000Sub001Block029Part005
    + surrogateDiagTailX0RatChunk000Sub001Block029Part006
    + surrogateDiagTailX0RatChunk000Sub001Block029Part007
    + surrogateDiagTailX0RatChunk000Sub001Block029Part008
    + surrogateDiagTailX0RatChunk000Sub001Block029Part009
    + surrogateDiagTailX0RatChunk000Sub001Block029Part010
    + surrogateDiagTailX0RatChunk000Sub001Block029Part011
    + surrogateDiagTailX0RatChunk000Sub001Block029Part012
    + surrogateDiagTailX0RatChunk000Sub001Block029Part013
    + surrogateDiagTailX0RatChunk000Sub001Block029Part014
    + surrogateDiagTailX0RatChunk000Sub001Block029Part015
    + surrogateDiagTailX0RatChunk000Sub001Block029Part016
    + surrogateDiagTailX0RatChunk000Sub001Block029Part017
    + surrogateDiagTailX0RatChunk000Sub001Block029Part018
    + surrogateDiagTailX0RatChunk000Sub001Block029Part019
    + surrogateDiagTailX0RatChunk000Sub001Block029Part020
    + surrogateDiagTailX0RatChunk000Sub001Block029Part021
    + surrogateDiagTailX0RatChunk000Sub001Block029Part022
    + surrogateDiagTailX0RatChunk000Sub001Block029Part023
    + surrogateDiagTailX0RatChunk000Sub001Block029Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block029_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block029Head + surrogateDiagTailX0RatChunk000Sub001Block029Mid + surrogateDiagTailX0RatChunk000Sub001Block029Tail =
      surrogateDiagTailX0RatChunk000Sub001Block029 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block029Head surrogateDiagTailX0RatChunk000Sub001Block029Mid surrogateDiagTailX0RatChunk000Sub001Block029Tail surrogateDiagTailX0RatChunk000Sub001Block029
  ring

def SurrogateDiagonalTailChunk000Sub001Block029HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block029HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block029Head

def SurrogateDiagonalTailChunk000Sub001Block029MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block029MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block029Mid

def SurrogateDiagonalTailChunk000Sub001Block029TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block029TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block029Tail

theorem surrogateDiagonalTailChunk000Sub001Block029_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block029HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block029MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block029TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block029Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block029 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block029HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block029MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block029TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block029Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block029_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
