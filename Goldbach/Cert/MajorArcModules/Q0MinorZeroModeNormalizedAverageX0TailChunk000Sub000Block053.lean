import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [53,54). -/

/- Block 053 covers tail-support indices [1325,1350) and q from 2233 to 2270. -/

def TailChunk000Sub000Block053Part000SupportExplicit : Finset ℕ :=
  ([2233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part000 : ℚ :=
  (1047372499 : ℚ) / 31870139793408

def SurrogateDiagonalTailChunk000Sub000Block053Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2233
    = surrogateDiagTailX0RatChunk000Sub000Block053Part000

theorem surrogateDiagonalTailChunk000Sub000Block053Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part000] using hcert

def TailChunk000Sub000Block053Part001SupportExplicit : Finset ℕ :=
  ([2234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part001 : ℚ :=
  (194795445125 : ℚ) / 1939338600081984

def SurrogateDiagonalTailChunk000Sub000Block053Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2234
    = surrogateDiagTailX0RatChunk000Sub000Block053Part001

theorem surrogateDiagonalTailChunk000Sub000Block053Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part001] using hcert

def TailChunk000Sub000Block053Part002SupportExplicit : Finset ℕ :=
  ([2235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part002 : ℚ :=
  (113565165675 : ℚ) / 1637994403987456

def SurrogateDiagonalTailChunk000Sub000Block053Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2235
    = surrogateDiagTailX0RatChunk000Sub000Block053Part002

theorem surrogateDiagonalTailChunk000Sub000Block053Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part002] using hcert

def TailChunk000Sub000Block053Part003SupportExplicit : Finset ℕ :=
  ([2237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part003 : ℚ :=
  (625396020775 : ℚ) / 62504898711086208

def SurrogateDiagonalTailChunk000Sub000Block053Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2237
    = surrogateDiagTailX0RatChunk000Sub000Block053Part003

theorem surrogateDiagonalTailChunk000Sub000Block053Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part003] using hcert

def TailChunk000Sub000Block053Part004SupportExplicit : Finset ℕ :=
  ([2238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part004 : ℚ :=
  (242836977625 : ℚ) / 766158459291648

def SurrogateDiagonalTailChunk000Sub000Block053Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2238
    = surrogateDiagTailX0RatChunk000Sub000Block053Part004

theorem surrogateDiagonalTailChunk000Sub000Block053Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part004] using hcert

def TailChunk000Sub000Block053Part005SupportExplicit : Finset ℕ :=
  ([2239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part005 : ℚ :=
  (626514796975 : ℚ) / 62728830054199368

def SurrogateDiagonalTailChunk000Sub000Block053Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2239
    = surrogateDiagTailX0RatChunk000Sub000Block053Part005

theorem surrogateDiagonalTailChunk000Sub000Block053Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part005] using hcert

def TailChunk000Sub000Block053Part006SupportExplicit : Finset ℕ :=
  ([2242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part006 : ℚ :=
  (73776400225 : ℚ) / 742623797620512

def SurrogateDiagonalTailChunk000Sub000Block053Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2242
    = surrogateDiagTailX0RatChunk000Sub000Block053Part006

theorem surrogateDiagonalTailChunk000Sub000Block053Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part006] using hcert

def TailChunk000Sub000Block053Part007SupportExplicit : Finset ℕ :=
  ([2243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part007 : ℚ :=
  (314314786275 : ℚ) / 21059499096021016

def SurrogateDiagonalTailChunk000Sub000Block053Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2243
    = surrogateDiagTailX0RatChunk000Sub000Block053Part007

theorem surrogateDiagonalTailChunk000Sub000Block053Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part007] using hcert

def TailChunk000Sub000Block053Part008SupportExplicit : Finset ℕ :=
  ([2245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part008 : ℚ :=
  (171884327625 : ℚ) / 8595232434159616

def SurrogateDiagonalTailChunk000Sub000Block053Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2245
    = surrogateDiagTailX0RatChunk000Sub000Block053Part008

theorem surrogateDiagonalTailChunk000Sub000Block053Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part008] using hcert

def TailChunk000Sub000Block053Part009SupportExplicit : Finset ℕ :=
  ([2246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part009 : ℚ :=
  (157546540325 : ℚ) / 1981382354051364

def SurrogateDiagonalTailChunk000Sub000Block053Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2246
    = surrogateDiagTailX0RatChunk000Sub000Block053Part009

theorem surrogateDiagonalTailChunk000Sub000Block053Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part009] using hcert

def TailChunk000Sub000Block053Part010SupportExplicit : Finset ℕ :=
  ([2247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part010 : ℚ :=
  (12188150975 : ℚ) / 204562171773504

def SurrogateDiagonalTailChunk000Sub000Block053Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2247
    = surrogateDiagTailX0RatChunk000Sub000Block053Part010

theorem surrogateDiagonalTailChunk000Sub000Block053Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part010] using hcert

def TailChunk000Sub000Block053Part011SupportExplicit : Finset ℕ :=
  ([2249] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part011 : ℚ :=
  (293141313575 : ℚ) / 22690059516002304

def SurrogateDiagonalTailChunk000Sub000Block053Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2249
    = surrogateDiagTailX0RatChunk000Sub000Block053Part011

theorem surrogateDiagonalTailChunk000Sub000Block053Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part011] using hcert

def TailChunk000Sub000Block053Part012SupportExplicit : Finset ℕ :=
  ([2251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part012 : ℚ :=
  (25329937999 : ℚ) / 2563403203125000

def SurrogateDiagonalTailChunk000Sub000Block053Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2251
    = surrogateDiagTailX0RatChunk000Sub000Block053Part012

theorem surrogateDiagonalTailChunk000Sub000Block053Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part012] using hcert

def TailChunk000Sub000Block053Part013SupportExplicit : Finset ℕ :=
  ([2253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part013 : ℚ :=
  (22528341991 : ℚ) / 506351250000000

def SurrogateDiagonalTailChunk000Sub000Block053Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2253
    = surrogateDiagTailX0RatChunk000Sub000Block053Part013

theorem surrogateDiagonalTailChunk000Sub000Block053Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part013] using hcert

def TailChunk000Sub000Block053Part014SupportExplicit : Finset ℕ :=
  ([2255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part014 : ℚ :=
  (3731360303 : ℚ) / 131098214400000

def SurrogateDiagonalTailChunk000Sub000Block053Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2255
    = surrogateDiagTailX0RatChunk000Sub000Block053Part014

theorem surrogateDiagonalTailChunk000Sub000Block053Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part014] using hcert

def TailChunk000Sub000Block053Part015SupportExplicit : Finset ℕ :=
  ([2257] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part015 : ℚ :=
  (4899133403 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block053Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2257
    = surrogateDiagTailX0RatChunk000Sub000Block053Part015

theorem surrogateDiagonalTailChunk000Sub000Block053Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part015] using hcert

def TailChunk000Sub000Block053Part016SupportExplicit : Finset ℕ :=
  ([2258] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part016 : ℚ :=
  (199003326125 : ℚ) / 2024106044580864

def SurrogateDiagonalTailChunk000Sub000Block053Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2258
    = surrogateDiagTailX0RatChunk000Sub000Block053Part016

theorem surrogateDiagonalTailChunk000Sub000Block053Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part016] using hcert

def TailChunk000Sub000Block053Part017SupportExplicit : Finset ℕ :=
  ([2261] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part017 : ℚ :=
  (168082971275 : ℚ) / 7431569723621376

def SurrogateDiagonalTailChunk000Sub000Block053Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2261
    = surrogateDiagTailX0RatChunk000Sub000Block053Part017

theorem surrogateDiagonalTailChunk000Sub000Block053Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part017] using hcert

def TailChunk000Sub000Block053Part018SupportExplicit : Finset ℕ :=
  ([2262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part018 : ℚ :=
  (28467661675 : ℚ) / 72846033813504

def SurrogateDiagonalTailChunk000Sub000Block053Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2262
    = surrogateDiagTailX0RatChunk000Sub000Block053Part018

theorem surrogateDiagonalTailChunk000Sub000Block053Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part018] using hcert

def TailChunk000Sub000Block053Part019SupportExplicit : Finset ℕ :=
  ([2263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part019 : ℚ :=
  (7241478851 : ℚ) / 435443538493440

def SurrogateDiagonalTailChunk000Sub000Block053Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2263
    = surrogateDiagTailX0RatChunk000Sub000Block053Part019

theorem surrogateDiagonalTailChunk000Sub000Block053Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part019] using hcert

def TailChunk000Sub000Block053Part020SupportExplicit : Finset ℕ :=
  ([2265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part020 : ℚ :=
  (871229833 : ℚ) / 12962592000000

def SurrogateDiagonalTailChunk000Sub000Block053Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2265
    = surrogateDiagTailX0RatChunk000Sub000Block053Part020

theorem surrogateDiagonalTailChunk000Sub000Block053Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part020] using hcert

def TailChunk000Sub000Block053Part021SupportExplicit : Finset ℕ :=
  ([2266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part021 : ℚ :=
  (11674692961 : ℚ) / 108264864643200

def SurrogateDiagonalTailChunk000Sub000Block053Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2266
    = surrogateDiagTailX0RatChunk000Sub000Block053Part021

theorem surrogateDiagonalTailChunk000Sub000Block053Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part021] using hcert

def TailChunk000Sub000Block053Part022SupportExplicit : Finset ℕ :=
  ([2267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part022 : ℚ :=
  (642282642775 : ℚ) / 65927480808429768

def SurrogateDiagonalTailChunk000Sub000Block053Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2267
    = surrogateDiagTailX0RatChunk000Sub000Block053Part022

theorem surrogateDiagonalTailChunk000Sub000Block053Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part022] using hcert

def TailChunk000Sub000Block053Part023SupportExplicit : Finset ℕ :=
  ([2269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part023 : ℚ :=
  (643416415975 : ℚ) / 66160542820111488

def SurrogateDiagonalTailChunk000Sub000Block053Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2269
    = surrogateDiagTailX0RatChunk000Sub000Block053Part023

theorem surrogateDiagonalTailChunk000Sub000Block053Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part023] using hcert

def TailChunk000Sub000Block053Part024SupportExplicit : Finset ℕ :=
  ([2270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block053Part024 : ℚ :=
  (263060355025 : ℚ) / 1669938897635328

def SurrogateDiagonalTailChunk000Sub000Block053Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2270
    = surrogateDiagTailX0RatChunk000Sub000Block053Part024

theorem surrogateDiagonalTailChunk000Sub000Block053Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block053Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block053Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block053Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block053Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block053Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block053HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block053Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block053Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block053Part000
    + surrogateDiagTailX0RatChunk000Sub000Block053Part001
    + surrogateDiagTailX0RatChunk000Sub000Block053Part002
    + surrogateDiagTailX0RatChunk000Sub000Block053Part003
    + surrogateDiagTailX0RatChunk000Sub000Block053Part004
    + surrogateDiagTailX0RatChunk000Sub000Block053Part005
    + surrogateDiagTailX0RatChunk000Sub000Block053Part006
    + surrogateDiagTailX0RatChunk000Sub000Block053Part007
    + surrogateDiagTailX0RatChunk000Sub000Block053Part008
    + surrogateDiagTailX0RatChunk000Sub000Block053Part009

def surrogateDiagonalTailChunk000Sub000Block053MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block053Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block053Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block053Part010
    + surrogateDiagTailX0RatChunk000Sub000Block053Part011
    + surrogateDiagTailX0RatChunk000Sub000Block053Part012
    + surrogateDiagTailX0RatChunk000Sub000Block053Part013
    + surrogateDiagTailX0RatChunk000Sub000Block053Part014
    + surrogateDiagTailX0RatChunk000Sub000Block053Part015
    + surrogateDiagTailX0RatChunk000Sub000Block053Part016
    + surrogateDiagTailX0RatChunk000Sub000Block053Part017
    + surrogateDiagTailX0RatChunk000Sub000Block053Part018
    + surrogateDiagTailX0RatChunk000Sub000Block053Part019

def surrogateDiagonalTailChunk000Sub000Block053TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block053Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block053Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block053Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block053Part020
    + surrogateDiagTailX0RatChunk000Sub000Block053Part021
    + surrogateDiagTailX0RatChunk000Sub000Block053Part022
    + surrogateDiagTailX0RatChunk000Sub000Block053Part023
    + surrogateDiagTailX0RatChunk000Sub000Block053Part024

def surrogateDiagonalTailChunk000Sub000Block053Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block053HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block053MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block053TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block053 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block053Part000
    + surrogateDiagTailX0RatChunk000Sub000Block053Part001
    + surrogateDiagTailX0RatChunk000Sub000Block053Part002
    + surrogateDiagTailX0RatChunk000Sub000Block053Part003
    + surrogateDiagTailX0RatChunk000Sub000Block053Part004
    + surrogateDiagTailX0RatChunk000Sub000Block053Part005
    + surrogateDiagTailX0RatChunk000Sub000Block053Part006
    + surrogateDiagTailX0RatChunk000Sub000Block053Part007
    + surrogateDiagTailX0RatChunk000Sub000Block053Part008
    + surrogateDiagTailX0RatChunk000Sub000Block053Part009
    + surrogateDiagTailX0RatChunk000Sub000Block053Part010
    + surrogateDiagTailX0RatChunk000Sub000Block053Part011
    + surrogateDiagTailX0RatChunk000Sub000Block053Part012
    + surrogateDiagTailX0RatChunk000Sub000Block053Part013
    + surrogateDiagTailX0RatChunk000Sub000Block053Part014
    + surrogateDiagTailX0RatChunk000Sub000Block053Part015
    + surrogateDiagTailX0RatChunk000Sub000Block053Part016
    + surrogateDiagTailX0RatChunk000Sub000Block053Part017
    + surrogateDiagTailX0RatChunk000Sub000Block053Part018
    + surrogateDiagTailX0RatChunk000Sub000Block053Part019
    + surrogateDiagTailX0RatChunk000Sub000Block053Part020
    + surrogateDiagTailX0RatChunk000Sub000Block053Part021
    + surrogateDiagTailX0RatChunk000Sub000Block053Part022
    + surrogateDiagTailX0RatChunk000Sub000Block053Part023
    + surrogateDiagTailX0RatChunk000Sub000Block053Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block053_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block053Head + surrogateDiagTailX0RatChunk000Sub000Block053Mid + surrogateDiagTailX0RatChunk000Sub000Block053Tail =
      surrogateDiagTailX0RatChunk000Sub000Block053 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block053Head surrogateDiagTailX0RatChunk000Sub000Block053Mid surrogateDiagTailX0RatChunk000Sub000Block053Tail surrogateDiagTailX0RatChunk000Sub000Block053
  ring

def SurrogateDiagonalTailChunk000Sub000Block053HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block053HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block053Head

def SurrogateDiagonalTailChunk000Sub000Block053MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block053MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block053Mid

def SurrogateDiagonalTailChunk000Sub000Block053TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block053TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block053Tail

theorem surrogateDiagonalTailChunk000Sub000Block053_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block053HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block053MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block053TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block053Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block053 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block053HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block053MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block053TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block053Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block053_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
