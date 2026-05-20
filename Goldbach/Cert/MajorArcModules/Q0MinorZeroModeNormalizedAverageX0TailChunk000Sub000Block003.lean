import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [3,4). -/

/- Block 003 covers tail-support indices [75,100) and q from 177 to 213. -/

def TailChunk000Sub000Block003Part000SupportExplicit : Finset ℕ :=
  ([177] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part000 : ℚ :=
  (36784556425 : ℚ) / 452750371968

def SurrogateDiagonalTailChunk000Sub000Block003Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 177
    = surrogateDiagTailX0RatChunk000Sub000Block003Part000

theorem surrogateDiagonalTailChunk000Sub000Block003Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part000] using hcert

def TailChunk000Sub000Block003Part001SupportExplicit : Finset ℕ :=
  ([178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part001 : ℚ :=
  (1162604775 : ℚ) / 6248076032

def SurrogateDiagonalTailChunk000Sub000Block003Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 178
    = surrogateDiagTailX0RatChunk000Sub000Block003Part001

theorem surrogateDiagonalTailChunk000Sub000Block003Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part001] using hcert

def TailChunk000Sub000Block003Part002SupportExplicit : Finset ℕ :=
  ([179] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part002 : ℚ :=
  (27884481275 : ℚ) / 1255095788964

def SurrogateDiagonalTailChunk000Sub000Block003Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 179
    = surrogateDiagTailX0RatChunk000Sub000Block003Part002

theorem surrogateDiagonalTailChunk000Sub000Block003Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part002] using hcert

def TailChunk000Sub000Block003Part003SupportExplicit : Finset ℕ :=
  ([181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part003 : ℚ :=
  (1140443171 : ℚ) / 52498497600

def SurrogateDiagonalTailChunk000Sub000Block003Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 181
    = surrogateDiagTailX0RatChunk000Sub000Block003Part003

theorem surrogateDiagonalTailChunk000Sub000Block003Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part003] using hcert

def TailChunk000Sub000Block003Part004SupportExplicit : Finset ℕ :=
  ([182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part004 : ℚ :=
  (6517525 : ℚ) / 19443888

def SurrogateDiagonalTailChunk000Sub000Block003Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 182
    = surrogateDiagTailX0RatChunk000Sub000Block003Part004

theorem surrogateDiagonalTailChunk000Sub000Block003Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part004] using hcert

def TailChunk000Sub000Block003Part005SupportExplicit : Finset ℕ :=
  ([183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part005 : ℚ :=
  (1491893959 : ℚ) / 20740147200

def SurrogateDiagonalTailChunk000Sub000Block003Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 183
    = surrogateDiagTailX0RatChunk000Sub000Block003Part005

theorem surrogateDiagonalTailChunk000Sub000Block003Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part005] using hcert

def TailChunk000Sub000Block003Part006SupportExplicit : Finset ℕ :=
  ([185] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part006 : ℚ :=
  (22483120625 : ℚ) / 537584615424

def SurrogateDiagonalTailChunk000Sub000Block003Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 185
    = surrogateDiagTailX0RatChunk000Sub000Block003Part006

theorem surrogateDiagonalTailChunk000Sub000Block003Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part006] using hcert

def TailChunk000Sub000Block003Part007SupportExplicit : Finset ℕ :=
  ([186] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part007 : ℚ :=
  (751097209 : ℚ) / 1296259200

def SurrogateDiagonalTailChunk000Sub000Block003Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 186
    = surrogateDiagTailX0RatChunk000Sub000Block003Part007

theorem surrogateDiagonalTailChunk000Sub000Block003Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part007] using hcert

def TailChunk000Sub000Block003Part008SupportExplicit : Finset ℕ :=
  ([187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part008 : ℚ :=
  (2016979711 : ℚ) / 65549107200

def SurrogateDiagonalTailChunk000Sub000Block003Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 187
    = surrogateDiagTailX0RatChunk000Sub000Block003Part008

theorem surrogateDiagonalTailChunk000Sub000Block003Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part008] using hcert

def TailChunk000Sub000Block003Part009SupportExplicit : Finset ℕ :=
  ([190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part009 : ℚ :=
  (5577744325 : ℚ) / 16799519232

def SurrogateDiagonalTailChunk000Sub000Block003Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 190
    = surrogateDiagTailX0RatChunk000Sub000Block003Part009

theorem surrogateDiagonalTailChunk000Sub000Block003Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part009] using hcert

def TailChunk000Sub000Block003Part010SupportExplicit : Finset ℕ :=
  ([191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part010 : ℚ :=
  (94376347 : ℚ) / 5213882568

def SurrogateDiagonalTailChunk000Sub000Block003Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 191
    = surrogateDiagTailX0RatChunk000Sub000Block003Part010

theorem surrogateDiagonalTailChunk000Sub000Block003Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part010] using hcert

def TailChunk000Sub000Block003Part011SupportExplicit : Finset ℕ :=
  ([193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part011 : ℚ :=
  (60226976875 : ℚ) / 3398065717248

def SurrogateDiagonalTailChunk000Sub000Block003Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 193
    = surrogateDiagTailX0RatChunk000Sub000Block003Part011

theorem surrogateDiagonalTailChunk000Sub000Block003Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part011] using hcert

def TailChunk000Sub000Block003Part012SupportExplicit : Finset ℕ :=
  ([194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part012 : ℚ :=
  (15133670825 : ℚ) / 106189553664

def SurrogateDiagonalTailChunk000Sub000Block003Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 194
    = surrogateDiagTailX0RatChunk000Sub000Block003Part012

theorem surrogateDiagonalTailChunk000Sub000Block003Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part012] using hcert

def TailChunk000Sub000Block003Part013SupportExplicit : Finset ℕ :=
  ([195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part013 : ℚ :=
  (7439092375 : ℚ) / 53094776832

def SurrogateDiagonalTailChunk000Sub000Block003Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 195
    = surrogateDiagTailX0RatChunk000Sub000Block003Part013

theorem surrogateDiagonalTailChunk000Sub000Block003Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part013] using hcert

def TailChunk000Sub000Block003Part014SupportExplicit : Finset ℕ :=
  ([197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part014 : ℚ :=
  (7543499375 : ℚ) / 461276316816

def SurrogateDiagonalTailChunk000Sub000Block003Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 197
    = surrogateDiagTailX0RatChunk000Sub000Block003Part014

theorem surrogateDiagonalTailChunk000Sub000Block003Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part014] using hcert

def TailChunk000Sub000Block003Part015SupportExplicit : Finset ℕ :=
  ([199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part015 : ℚ :=
  (7697444375 : ℚ) / 480394064601

def SurrogateDiagonalTailChunk000Sub000Block003Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 199
    = surrogateDiagTailX0RatChunk000Sub000Block003Part015

theorem surrogateDiagonalTailChunk000Sub000Block003Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part015] using hcert

def TailChunk000Sub000Block003Part016SupportExplicit : Finset ℕ :=
  ([201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part016 : ℚ :=
  (1381775 : ℚ) / 25299648

def SurrogateDiagonalTailChunk000Sub000Block003Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 201
    = surrogateDiagTailX0RatChunk000Sub000Block003Part016

theorem surrogateDiagonalTailChunk000Sub000Block003Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part016] using hcert

def TailChunk000Sub000Block003Part017SupportExplicit : Finset ℕ :=
  ([202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part017 : ℚ :=
  (50505151 : ℚ) / 400080000

def SurrogateDiagonalTailChunk000Sub000Block003Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 202
    = surrogateDiagTailX0RatChunk000Sub000Block003Part017

theorem surrogateDiagonalTailChunk000Sub000Block003Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part017] using hcert

def TailChunk000Sub000Block003Part018SupportExplicit : Finset ℕ :=
  ([203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part018 : ℚ :=
  (51409307725 : ℚ) / 1991883737088

def SurrogateDiagonalTailChunk000Sub000Block003Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 203
    = surrogateDiagTailX0RatChunk000Sub000Block003Part018

theorem surrogateDiagonalTailChunk000Sub000Block003Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part018] using hcert

def TailChunk000Sub000Block003Part019SupportExplicit : Finset ℕ :=
  ([205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part019 : ℚ :=
  (1977226669 : ℚ) / 65549107200

def SurrogateDiagonalTailChunk000Sub000Block003Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 205
    = surrogateDiagTailX0RatChunk000Sub000Block003Part019

theorem surrogateDiagonalTailChunk000Sub000Block003Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part019] using hcert

def TailChunk000Sub000Block003Part020SupportExplicit : Finset ℕ :=
  ([206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part020 : ℚ :=
  (437886475 : ℚ) / 3759196689

def SurrogateDiagonalTailChunk000Sub000Block003Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 206
    = surrogateDiagTailX0RatChunk000Sub000Block003Part020

theorem surrogateDiagonalTailChunk000Sub000Block003Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part020] using hcert

def TailChunk000Sub000Block003Part021SupportExplicit : Finset ℕ :=
  ([209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part021 : ℚ :=
  (752186203 : ℚ) / 34998998400

def SurrogateDiagonalTailChunk000Sub000Block003Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 209
    = surrogateDiagTailX0RatChunk000Sub000Block003Part021

theorem surrogateDiagonalTailChunk000Sub000Block003Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part021] using hcert

def TailChunk000Sub000Block003Part022SupportExplicit : Finset ℕ :=
  ([210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part022 : ℚ :=
  (208945075 : ℚ) / 184356864

def SurrogateDiagonalTailChunk000Sub000Block003Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 210
    = surrogateDiagTailX0RatChunk000Sub000Block003Part022

theorem surrogateDiagonalTailChunk000Sub000Block003Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part022] using hcert

def TailChunk000Sub000Block003Part023SupportExplicit : Finset ℕ :=
  ([211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part023 : ℚ :=
  (3517159 : ℚ) / 257301450

def SurrogateDiagonalTailChunk000Sub000Block003Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 211
    = surrogateDiagTailX0RatChunk000Sub000Block003Part023

theorem surrogateDiagonalTailChunk000Sub000Block003Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part023] using hcert

def TailChunk000Sub000Block003Part024SupportExplicit : Finset ℕ :=
  ([213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block003Part024 : ℚ :=
  (1727750461 : ℚ) / 38423683200

def SurrogateDiagonalTailChunk000Sub000Block003Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 213
    = surrogateDiagTailX0RatChunk000Sub000Block003Part024

theorem surrogateDiagonalTailChunk000Sub000Block003Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block003Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block003Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block003Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block003Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block003Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block003HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block003Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block003Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block003Part000
    + surrogateDiagTailX0RatChunk000Sub000Block003Part001
    + surrogateDiagTailX0RatChunk000Sub000Block003Part002
    + surrogateDiagTailX0RatChunk000Sub000Block003Part003
    + surrogateDiagTailX0RatChunk000Sub000Block003Part004
    + surrogateDiagTailX0RatChunk000Sub000Block003Part005
    + surrogateDiagTailX0RatChunk000Sub000Block003Part006
    + surrogateDiagTailX0RatChunk000Sub000Block003Part007
    + surrogateDiagTailX0RatChunk000Sub000Block003Part008
    + surrogateDiagTailX0RatChunk000Sub000Block003Part009

def surrogateDiagonalTailChunk000Sub000Block003MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block003Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block003Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block003Part010
    + surrogateDiagTailX0RatChunk000Sub000Block003Part011
    + surrogateDiagTailX0RatChunk000Sub000Block003Part012
    + surrogateDiagTailX0RatChunk000Sub000Block003Part013
    + surrogateDiagTailX0RatChunk000Sub000Block003Part014
    + surrogateDiagTailX0RatChunk000Sub000Block003Part015
    + surrogateDiagTailX0RatChunk000Sub000Block003Part016
    + surrogateDiagTailX0RatChunk000Sub000Block003Part017
    + surrogateDiagTailX0RatChunk000Sub000Block003Part018
    + surrogateDiagTailX0RatChunk000Sub000Block003Part019

def surrogateDiagonalTailChunk000Sub000Block003TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block003Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block003Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block003Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block003Part020
    + surrogateDiagTailX0RatChunk000Sub000Block003Part021
    + surrogateDiagTailX0RatChunk000Sub000Block003Part022
    + surrogateDiagTailX0RatChunk000Sub000Block003Part023
    + surrogateDiagTailX0RatChunk000Sub000Block003Part024

def surrogateDiagonalTailChunk000Sub000Block003Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block003HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block003MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block003TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block003 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block003Part000
    + surrogateDiagTailX0RatChunk000Sub000Block003Part001
    + surrogateDiagTailX0RatChunk000Sub000Block003Part002
    + surrogateDiagTailX0RatChunk000Sub000Block003Part003
    + surrogateDiagTailX0RatChunk000Sub000Block003Part004
    + surrogateDiagTailX0RatChunk000Sub000Block003Part005
    + surrogateDiagTailX0RatChunk000Sub000Block003Part006
    + surrogateDiagTailX0RatChunk000Sub000Block003Part007
    + surrogateDiagTailX0RatChunk000Sub000Block003Part008
    + surrogateDiagTailX0RatChunk000Sub000Block003Part009
    + surrogateDiagTailX0RatChunk000Sub000Block003Part010
    + surrogateDiagTailX0RatChunk000Sub000Block003Part011
    + surrogateDiagTailX0RatChunk000Sub000Block003Part012
    + surrogateDiagTailX0RatChunk000Sub000Block003Part013
    + surrogateDiagTailX0RatChunk000Sub000Block003Part014
    + surrogateDiagTailX0RatChunk000Sub000Block003Part015
    + surrogateDiagTailX0RatChunk000Sub000Block003Part016
    + surrogateDiagTailX0RatChunk000Sub000Block003Part017
    + surrogateDiagTailX0RatChunk000Sub000Block003Part018
    + surrogateDiagTailX0RatChunk000Sub000Block003Part019
    + surrogateDiagTailX0RatChunk000Sub000Block003Part020
    + surrogateDiagTailX0RatChunk000Sub000Block003Part021
    + surrogateDiagTailX0RatChunk000Sub000Block003Part022
    + surrogateDiagTailX0RatChunk000Sub000Block003Part023
    + surrogateDiagTailX0RatChunk000Sub000Block003Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block003_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block003Head + surrogateDiagTailX0RatChunk000Sub000Block003Mid + surrogateDiagTailX0RatChunk000Sub000Block003Tail =
      surrogateDiagTailX0RatChunk000Sub000Block003 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block003Head surrogateDiagTailX0RatChunk000Sub000Block003Mid surrogateDiagTailX0RatChunk000Sub000Block003Tail surrogateDiagTailX0RatChunk000Sub000Block003
  ring

def SurrogateDiagonalTailChunk000Sub000Block003HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block003HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block003Head

def SurrogateDiagonalTailChunk000Sub000Block003MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block003MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block003Mid

def SurrogateDiagonalTailChunk000Sub000Block003TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block003TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block003Tail

theorem surrogateDiagonalTailChunk000Sub000Block003_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block003HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block003MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block003TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block003Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block003 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block003HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block003MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block003TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block003Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block003_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
