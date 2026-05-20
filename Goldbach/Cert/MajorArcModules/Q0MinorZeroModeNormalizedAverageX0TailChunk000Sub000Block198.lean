import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [198,199). -/

/-- Block 198 covers tail-support indices [4950,4975) and q from 8191 to 8230. -/

def TailChunk000Sub000Block198Part000SupportExplicit : Finset ℕ :=
  ([8191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block198Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8191
    = surrogateDiagTailX0RatChunk000Sub000Block198Part000

theorem surrogateDiagonalTailChunk000Sub000Block198Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part000] using hcert

def TailChunk000Sub000Block198Part001SupportExplicit : Finset ℕ :=
  ([8193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part001 : ℚ :=
  (266532211 : ℚ) / 1269870344084160

def SurrogateDiagonalTailChunk000Sub000Block198Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8193
    = surrogateDiagTailX0RatChunk000Sub000Block198Part001

theorem surrogateDiagonalTailChunk000Sub000Block198Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part001] using hcert

def TailChunk000Sub000Block198Part002SupportExplicit : Finset ℕ :=
  ([8194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part002 : ℚ :=
  (39950764387 : ℚ) / 21747620590387200

def SurrogateDiagonalTailChunk000Sub000Block198Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8194
    = surrogateDiagTailX0RatChunk000Sub000Block198Part002

theorem surrogateDiagonalTailChunk000Sub000Block198Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part002] using hcert

def TailChunk000Sub000Block198Part003SupportExplicit : Finset ℕ :=
  ([8195] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part003 : ℚ :=
  (1569919329 : ℚ) / 8189972019937280

def SurrogateDiagonalTailChunk000Sub000Block198Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8195
    = surrogateDiagTailX0RatChunk000Sub000Block198Part003

theorem surrogateDiagonalTailChunk000Sub000Block198Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part003] using hcert

def TailChunk000Sub000Block198Part004SupportExplicit : Finset ℕ :=
  ([8197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part004 : ℚ :=
  (136989520963 : ℚ) / 242904353572483200

def SurrogateDiagonalTailChunk000Sub000Block198Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8197
    = surrogateDiagTailX0RatChunk000Sub000Block198Part004

theorem surrogateDiagonalTailChunk000Sub000Block198Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part004] using hcert

def TailChunk000Sub000Block198Part005SupportExplicit : Finset ℕ :=
  ([8198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part005 : ℚ :=
  (2099805079975 : ℚ) / 705203850839694408

def SurrogateDiagonalTailChunk000Sub000Block198Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8198
    = surrogateDiagTailX0RatChunk000Sub000Block198Part005

theorem surrogateDiagonalTailChunk000Sub000Block198Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part005] using hcert

def TailChunk000Sub000Block198Part006SupportExplicit : Finset ℕ :=
  ([8201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part006 : ℚ :=
  (8362781675 : ℚ) / 21116352806982848

def SurrogateDiagonalTailChunk000Sub000Block198Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8201
    = surrogateDiagTailX0RatChunk000Sub000Block198Part006

theorem surrogateDiagonalTailChunk000Sub000Block198Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part006] using hcert

def TailChunk000Sub000Block198Part007SupportExplicit : Finset ℕ :=
  ([8202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part007 : ℚ :=
  (583493467475 : ℚ) / 69649763045895744

def SurrogateDiagonalTailChunk000Sub000Block198Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8202
    = surrogateDiagTailX0RatChunk000Sub000Block198Part007

theorem surrogateDiagonalTailChunk000Sub000Block198Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part007] using hcert

def TailChunk000Sub000Block198Part008SupportExplicit : Finset ℕ :=
  ([8203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part008 : ℚ :=
  (75002272001 : ℚ) / 163359364987929600

def SurrogateDiagonalTailChunk000Sub000Block198Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8203
    = surrogateDiagTailX0RatChunk000Sub000Block198Part008

theorem surrogateDiagonalTailChunk000Sub000Block198Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part008] using hcert

def TailChunk000Sub000Block198Part009SupportExplicit : Finset ℕ :=
  ([8205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part009 : ℚ :=
  (1854216275 : ℚ) / 972481904529408

def SurrogateDiagonalTailChunk000Sub000Block198Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8205
    = surrogateDiagTailX0RatChunk000Sub000Block198Part009

theorem surrogateDiagonalTailChunk000Sub000Block198Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part009] using hcert

def TailChunk000Sub000Block198Part010SupportExplicit : Finset ℕ :=
  ([8206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part010 : ℚ :=
  (94362775 : ℚ) / 24714789009408

def SurrogateDiagonalTailChunk000Sub000Block198Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8206
    = surrogateDiagTailX0RatChunk000Sub000Block198Part010

theorem surrogateDiagonalTailChunk000Sub000Block198Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part010] using hcert

def TailChunk000Sub000Block198Part011SupportExplicit : Finset ℕ :=
  ([8207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part011 : ℚ :=
  (73898626325 : ℚ) / 179995504186616832

def SurrogateDiagonalTailChunk000Sub000Block198Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8207
    = surrogateDiagTailX0RatChunk000Sub000Block198Part011

theorem surrogateDiagonalTailChunk000Sub000Block198Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part011] using hcert

def TailChunk000Sub000Block198Part012SupportExplicit : Finset ℕ :=
  ([8209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part012 : ℚ :=
  (1052932515625 : ℚ) / 2837371869000179712

def SurrogateDiagonalTailChunk000Sub000Block198Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8209
    = surrogateDiagTailX0RatChunk000Sub000Block198Part012

theorem surrogateDiagonalTailChunk000Sub000Block198Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part012] using hcert

def TailChunk000Sub000Block198Part013SupportExplicit : Finset ℕ :=
  ([8210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part013 : ℚ :=
  (6057268399 : ℚ) / 1157663191941120

def SurrogateDiagonalTailChunk000Sub000Block198Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8210
    = surrogateDiagTailX0RatChunk000Sub000Block198Part013

theorem surrogateDiagonalTailChunk000Sub000Block198Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part013] using hcert

def TailChunk000Sub000Block198Part014SupportExplicit : Finset ℕ :=
  ([8211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part014 : ℚ :=
  (1677262452625 : ℚ) / 796017282659647488

def SurrogateDiagonalTailChunk000Sub000Block198Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8211
    = surrogateDiagTailX0RatChunk000Sub000Block198Part014

theorem surrogateDiagonalTailChunk000Sub000Block198Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part014] using hcert

def TailChunk000Sub000Block198Part015SupportExplicit : Finset ℕ :=
  ([8213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part015 : ℚ :=
  (162008179147 : ℚ) / 405600438282883200

def SurrogateDiagonalTailChunk000Sub000Block198Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8213
    = surrogateDiagTailX0RatChunk000Sub000Block198Part015

theorem surrogateDiagonalTailChunk000Sub000Block198Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part015] using hcert

def TailChunk000Sub000Block198Part016SupportExplicit : Finset ℕ :=
  ([8215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part016 : ℚ :=
  (22691958329 : ℚ) / 30328798421975040

def SurrogateDiagonalTailChunk000Sub000Block198Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8215
    = surrogateDiagTailX0RatChunk000Sub000Block198Part016

theorem surrogateDiagonalTailChunk000Sub000Block198Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part016] using hcert

def TailChunk000Sub000Block198Part017SupportExplicit : Finset ℕ :=
  ([8218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part017 : ℚ :=
  (946382789125 : ℚ) / 382139846210544768

def SurrogateDiagonalTailChunk000Sub000Block198Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8218
    = surrogateDiagTailX0RatChunk000Sub000Block198Part017

theorem surrogateDiagonalTailChunk000Sub000Block198Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part017] using hcert

def TailChunk000Sub000Block198Part018SupportExplicit : Finset ℕ :=
  ([8219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part018 : ℚ :=
  (1055499390625 : ℚ) / 2851224507096854322

def SurrogateDiagonalTailChunk000Sub000Block198Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8219
    = surrogateDiagTailX0RatChunk000Sub000Block198Part018

theorem surrogateDiagonalTailChunk000Sub000Block198Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part018] using hcert

def TailChunk000Sub000Block198Part019SupportExplicit : Finset ℕ :=
  ([8221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part019 : ℚ :=
  (1689621025 : ℚ) / 4566401776295712

def SurrogateDiagonalTailChunk000Sub000Block198Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8221
    = surrogateDiagTailX0RatChunk000Sub000Block198Part019

theorem surrogateDiagonalTailChunk000Sub000Block198Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part019] using hcert

def TailChunk000Sub000Block198Part020SupportExplicit : Finset ℕ :=
  ([8222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part020 : ℚ :=
  (422508025 : ℚ) / 285400111018482

def SurrogateDiagonalTailChunk000Sub000Block198Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8222
    = surrogateDiagTailX0RatChunk000Sub000Block198Part020

theorem surrogateDiagonalTailChunk000Sub000Block198Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part020] using hcert

def TailChunk000Sub000Block198Part021SupportExplicit : Finset ℕ :=
  ([8223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part021 : ℚ :=
  (46942504979 : ℚ) / 45100264457241600

def SurrogateDiagonalTailChunk000Sub000Block198Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8223
    = surrogateDiagTailX0RatChunk000Sub000Block198Part021

theorem surrogateDiagonalTailChunk000Sub000Block198Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part021] using hcert

def TailChunk000Sub000Block198Part022SupportExplicit : Finset ℕ :=
  ([8227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part022 : ℚ :=
  (3913708405375 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub000Block198Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8227
    = surrogateDiagTailX0RatChunk000Sub000Block198Part022

theorem surrogateDiagonalTailChunk000Sub000Block198Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part022] using hcert

def TailChunk000Sub000Block198Part023SupportExplicit : Finset ℕ :=
  ([8229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part023 : ℚ :=
  (16886370197 : ℚ) / 12907406616330240

def SurrogateDiagonalTailChunk000Sub000Block198Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8229
    = surrogateDiagTailX0RatChunk000Sub000Block198Part023

theorem surrogateDiagonalTailChunk000Sub000Block198Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part023] using hcert

def TailChunk000Sub000Block198Part024SupportExplicit : Finset ℕ :=
  ([8230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block198Part024 : ℚ :=
  (888254005375 : ℚ) / 292249713682925568

def SurrogateDiagonalTailChunk000Sub000Block198Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8230
    = surrogateDiagTailX0RatChunk000Sub000Block198Part024

theorem surrogateDiagonalTailChunk000Sub000Block198Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block198Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block198Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block198Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block198Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block198Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block198HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block198Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block198Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part000
    + surrogateDiagTailX0RatChunk000Sub000Block198Part001
    + surrogateDiagTailX0RatChunk000Sub000Block198Part002
    + surrogateDiagTailX0RatChunk000Sub000Block198Part003
    + surrogateDiagTailX0RatChunk000Sub000Block198Part004
    + surrogateDiagTailX0RatChunk000Sub000Block198Part005
    + surrogateDiagTailX0RatChunk000Sub000Block198Part006
    + surrogateDiagTailX0RatChunk000Sub000Block198Part007
    + surrogateDiagTailX0RatChunk000Sub000Block198Part008
    + surrogateDiagTailX0RatChunk000Sub000Block198Part009

def surrogateDiagonalTailChunk000Sub000Block198MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block198Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block198Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part010
    + surrogateDiagTailX0RatChunk000Sub000Block198Part011
    + surrogateDiagTailX0RatChunk000Sub000Block198Part012
    + surrogateDiagTailX0RatChunk000Sub000Block198Part013
    + surrogateDiagTailX0RatChunk000Sub000Block198Part014
    + surrogateDiagTailX0RatChunk000Sub000Block198Part015
    + surrogateDiagTailX0RatChunk000Sub000Block198Part016
    + surrogateDiagTailX0RatChunk000Sub000Block198Part017
    + surrogateDiagTailX0RatChunk000Sub000Block198Part018
    + surrogateDiagTailX0RatChunk000Sub000Block198Part019

def surrogateDiagonalTailChunk000Sub000Block198TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block198Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block198Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block198Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part020
    + surrogateDiagTailX0RatChunk000Sub000Block198Part021
    + surrogateDiagTailX0RatChunk000Sub000Block198Part022
    + surrogateDiagTailX0RatChunk000Sub000Block198Part023
    + surrogateDiagTailX0RatChunk000Sub000Block198Part024

def surrogateDiagonalTailChunk000Sub000Block198Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block198HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block198MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block198TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block198 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block198Part000
    + surrogateDiagTailX0RatChunk000Sub000Block198Part001
    + surrogateDiagTailX0RatChunk000Sub000Block198Part002
    + surrogateDiagTailX0RatChunk000Sub000Block198Part003
    + surrogateDiagTailX0RatChunk000Sub000Block198Part004
    + surrogateDiagTailX0RatChunk000Sub000Block198Part005
    + surrogateDiagTailX0RatChunk000Sub000Block198Part006
    + surrogateDiagTailX0RatChunk000Sub000Block198Part007
    + surrogateDiagTailX0RatChunk000Sub000Block198Part008
    + surrogateDiagTailX0RatChunk000Sub000Block198Part009
    + surrogateDiagTailX0RatChunk000Sub000Block198Part010
    + surrogateDiagTailX0RatChunk000Sub000Block198Part011
    + surrogateDiagTailX0RatChunk000Sub000Block198Part012
    + surrogateDiagTailX0RatChunk000Sub000Block198Part013
    + surrogateDiagTailX0RatChunk000Sub000Block198Part014
    + surrogateDiagTailX0RatChunk000Sub000Block198Part015
    + surrogateDiagTailX0RatChunk000Sub000Block198Part016
    + surrogateDiagTailX0RatChunk000Sub000Block198Part017
    + surrogateDiagTailX0RatChunk000Sub000Block198Part018
    + surrogateDiagTailX0RatChunk000Sub000Block198Part019
    + surrogateDiagTailX0RatChunk000Sub000Block198Part020
    + surrogateDiagTailX0RatChunk000Sub000Block198Part021
    + surrogateDiagTailX0RatChunk000Sub000Block198Part022
    + surrogateDiagTailX0RatChunk000Sub000Block198Part023
    + surrogateDiagTailX0RatChunk000Sub000Block198Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block198_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block198Head + surrogateDiagTailX0RatChunk000Sub000Block198Mid + surrogateDiagTailX0RatChunk000Sub000Block198Tail =
      surrogateDiagTailX0RatChunk000Sub000Block198 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block198Head surrogateDiagTailX0RatChunk000Sub000Block198Mid surrogateDiagTailX0RatChunk000Sub000Block198Tail surrogateDiagTailX0RatChunk000Sub000Block198
  ring

def SurrogateDiagonalTailChunk000Sub000Block198HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block198HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block198Head

def SurrogateDiagonalTailChunk000Sub000Block198MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block198MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block198Mid

def SurrogateDiagonalTailChunk000Sub000Block198TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block198TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block198Tail

theorem surrogateDiagonalTailChunk000Sub000Block198_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block198HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block198MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block198TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block198Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block198 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block198HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block198MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block198TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block198Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block198_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
