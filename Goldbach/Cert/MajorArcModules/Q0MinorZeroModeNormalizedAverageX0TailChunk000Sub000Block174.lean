import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [174,175). -/

/-- Block 174 covers tail-support indices [4350,4375) and q from 7210 to 7247. -/

def TailChunk000Sub000Block174Part000SupportExplicit : Finset ℕ :=
  ([7210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part000 : ℚ :=
  (489191460275 : ℚ) / 44899604664827904

def SurrogateDiagonalTailChunk000Sub000Block174Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7210
    = surrogateDiagTailX0RatChunk000Sub000Block174Part000

theorem surrogateDiagonalTailChunk000Sub000Block174Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part000] using hcert

def TailChunk000Sub000Block174Part001SupportExplicit : Finset ℕ :=
  ([7211] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part001 : ℚ :=
  (1299963025 : ℚ) / 2702887122140562

def SurrogateDiagonalTailChunk000Sub000Block174Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7211
    = surrogateDiagTailX0RatChunk000Sub000Block174Part001

theorem surrogateDiagonalTailChunk000Sub000Block174Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part001] using hcert

def TailChunk000Sub000Block174Part002SupportExplicit : Finset ℕ :=
  ([7213] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part002 : ℚ :=
  (812927640625 : ℚ) / 1691179633009903392

def SurrogateDiagonalTailChunk000Sub000Block174Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7213
    = surrogateDiagTailX0RatChunk000Sub000Block174Part002

theorem surrogateDiagonalTailChunk000Sub000Block174Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part002] using hcert

def TailChunk000Sub000Block174Part003SupportExplicit : Finset ℕ :=
  ([7214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part003 : ℚ :=
  (1625980863775 : ℚ) / 422794908252475848

def SurrogateDiagonalTailChunk000Sub000Block174Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7214
    = surrogateDiagTailX0RatChunk000Sub000Block174Part003

theorem surrogateDiagonalTailChunk000Sub000Block174Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part003] using hcert

def TailChunk000Sub000Block174Part004SupportExplicit : Finset ℕ :=
  ([7215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part004 : ℚ :=
  (684206167375 : ℚ) / 356715346733826048

def SurrogateDiagonalTailChunk000Sub000Block174Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7215
    = surrogateDiagTailX0RatChunk000Sub000Block174Part004

theorem surrogateDiagonalTailChunk000Sub000Block174Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part004] using hcert

def TailChunk000Sub000Block174Part005SupportExplicit : Finset ℕ :=
  ([7217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part005 : ℚ :=
  (13325610691 : ℚ) / 145895114964355200

def SurrogateDiagonalTailChunk000Sub000Block174Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7217
    = surrogateDiagTailX0RatChunk000Sub000Block174Part005

theorem surrogateDiagonalTailChunk000Sub000Block174Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part005] using hcert

def TailChunk000Sub000Block174Part006SupportExplicit : Finset ℕ :=
  ([7219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7219
    = surrogateDiagTailX0RatChunk000Sub000Block174Part006

theorem surrogateDiagonalTailChunk000Sub000Block174Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part006] using hcert

def TailChunk000Sub000Block174Part007SupportExplicit : Finset ℕ :=
  ([7221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part007 : ℚ :=
  (17278709025 : ℚ) / 26471898322386944

def SurrogateDiagonalTailChunk000Sub000Block174Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7221
    = surrogateDiagTailX0RatChunk000Sub000Block174Part007

theorem surrogateDiagonalTailChunk000Sub000Block174Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part007] using hcert

def TailChunk000Sub000Block174Part008SupportExplicit : Finset ℕ :=
  ([7222] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part008 : ℚ :=
  (98784935825 : ℚ) / 43363665790638336

def SurrogateDiagonalTailChunk000Sub000Block174Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7222
    = surrogateDiagTailX0RatChunk000Sub000Block174Part008

theorem surrogateDiagonalTailChunk000Sub000Block174Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part008] using hcert

def TailChunk000Sub000Block174Part009SupportExplicit : Finset ℕ :=
  ([7223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part009 : ℚ :=
  (22911691 : ℚ) / 1618660640194560

def SurrogateDiagonalTailChunk000Sub000Block174Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7223
    = surrogateDiagTailX0RatChunk000Sub000Block174Part009

theorem surrogateDiagonalTailChunk000Sub000Block174Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part009] using hcert

def TailChunk000Sub000Block174Part010SupportExplicit : Finset ℕ :=
  ([7226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part010 : ℚ :=
  (203965140625 : ℚ) / 106403970503752992

def SurrogateDiagonalTailChunk000Sub000Block174Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7226
    = surrogateDiagTailX0RatChunk000Sub000Block174Part010

theorem surrogateDiagonalTailChunk000Sub000Block174Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part010] using hcert

def TailChunk000Sub000Block174Part011SupportExplicit : Finset ℕ :=
  ([7229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7229
    = surrogateDiagTailX0RatChunk000Sub000Block174Part011

theorem surrogateDiagonalTailChunk000Sub000Block174Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part011] using hcert

def TailChunk000Sub000Block174Part012SupportExplicit : Finset ℕ :=
  ([7230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part012 : ℚ :=
  (3615649 : ℚ) / 209757143040

def SurrogateDiagonalTailChunk000Sub000Block174Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7230
    = surrogateDiagTailX0RatChunk000Sub000Block174Part012

theorem surrogateDiagonalTailChunk000Sub000Block174Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part012] using hcert

def TailChunk000Sub000Block174Part013SupportExplicit : Finset ℕ :=
  ([7231] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part013 : ℚ :=
  (267970705525 : ℚ) / 3675789641592373248

def SurrogateDiagonalTailChunk000Sub000Block174Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7231
    = surrogateDiagTailX0RatChunk000Sub000Block174Part013

theorem surrogateDiagonalTailChunk000Sub000Block174Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part013] using hcert

def TailChunk000Sub000Block174Part014SupportExplicit : Finset ℕ :=
  ([7233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part014 : ℚ :=
  (14529843629 : ℚ) / 26992617932097600

def SurrogateDiagonalTailChunk000Sub000Block174Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7233
    = surrogateDiagTailX0RatChunk000Sub000Block174Part014

theorem surrogateDiagonalTailChunk000Sub000Block174Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part014] using hcert

def TailChunk000Sub000Block174Part015SupportExplicit : Finset ℕ :=
  ([7234] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part015 : ℚ :=
  (204417015625 : ℚ) / 106876089448660992

def SurrogateDiagonalTailChunk000Sub000Block174Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7234
    = surrogateDiagTailX0RatChunk000Sub000Block174Part015

theorem surrogateDiagonalTailChunk000Sub000Block174Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part015] using hcert

def TailChunk000Sub000Block174Part016SupportExplicit : Finset ℕ :=
  ([7235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part016 : ℚ :=
  (49142529275 : ℚ) / 349824328399984896

def SurrogateDiagonalTailChunk000Sub000Block174Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7235
    = surrogateDiagTailX0RatChunk000Sub000Block174Part016

theorem surrogateDiagonalTailChunk000Sub000Block174Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part016] using hcert

def TailChunk000Sub000Block174Part017SupportExplicit : Finset ℕ :=
  ([7237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7237
    = surrogateDiagTailX0RatChunk000Sub000Block174Part017

theorem surrogateDiagonalTailChunk000Sub000Block174Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part017] using hcert

def TailChunk000Sub000Block174Part018SupportExplicit : Finset ℕ :=
  ([7238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part018 : ℚ :=
  (3013816537 : ℚ) / 644882614732800

def SurrogateDiagonalTailChunk000Sub000Block174Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7238
    = surrogateDiagTailX0RatChunk000Sub000Block174Part018

theorem surrogateDiagonalTailChunk000Sub000Block174Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part018] using hcert

def TailChunk000Sub000Block174Part019SupportExplicit : Finset ℕ :=
  ([7239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part019 : ℚ :=
  (236300675 : ℚ) / 342911786563584

def SurrogateDiagonalTailChunk000Sub000Block174Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7239
    = surrogateDiagTailX0RatChunk000Sub000Block174Part019

theorem surrogateDiagonalTailChunk000Sub000Block174Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part019] using hcert

def TailChunk000Sub000Block174Part020SupportExplicit : Finset ℕ :=
  ([7241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part020 : ℚ :=
  (177362837275 : ℚ) / 4955083865762070528

def SurrogateDiagonalTailChunk000Sub000Block174Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7241
    = surrogateDiagTailX0RatChunk000Sub000Block174Part020

theorem surrogateDiagonalTailChunk000Sub000Block174Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part020] using hcert

def TailChunk000Sub000Block174Part021SupportExplicit : Finset ℕ :=
  ([7242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part021 : ℚ :=
  (23968192561 : ℚ) / 2518134502195200

def SurrogateDiagonalTailChunk000Sub000Block174Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7242
    = surrogateDiagTailX0RatChunk000Sub000Block174Part021

theorem surrogateDiagonalTailChunk000Sub000Block174Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part021] using hcert

def TailChunk000Sub000Block174Part022SupportExplicit : Finset ℕ :=
  ([7243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block174Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7243
    = surrogateDiagTailX0RatChunk000Sub000Block174Part022

theorem surrogateDiagonalTailChunk000Sub000Block174Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part022] using hcert

def TailChunk000Sub000Block174Part023SupportExplicit : Finset ℕ :=
  ([7246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part023 : ℚ :=
  (205095765625 : ℚ) / 107587211518085682

def SurrogateDiagonalTailChunk000Sub000Block174Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7246
    = surrogateDiagTailX0RatChunk000Sub000Block174Part023

theorem surrogateDiagonalTailChunk000Sub000Block174Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part023] using hcert

def TailChunk000Sub000Block174Part024SupportExplicit : Finset ℕ :=
  ([7247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block174Part024 : ℚ :=
  (820609515625 : ℚ) / 1723297215771459282

def SurrogateDiagonalTailChunk000Sub000Block174Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 7247
    = surrogateDiagTailX0RatChunk000Sub000Block174Part024

theorem surrogateDiagonalTailChunk000Sub000Block174Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block174Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block174Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block174Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block174Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block174Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block174HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block174Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block174Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part000
    + surrogateDiagTailX0RatChunk000Sub000Block174Part001
    + surrogateDiagTailX0RatChunk000Sub000Block174Part002
    + surrogateDiagTailX0RatChunk000Sub000Block174Part003
    + surrogateDiagTailX0RatChunk000Sub000Block174Part004
    + surrogateDiagTailX0RatChunk000Sub000Block174Part005
    + surrogateDiagTailX0RatChunk000Sub000Block174Part006
    + surrogateDiagTailX0RatChunk000Sub000Block174Part007
    + surrogateDiagTailX0RatChunk000Sub000Block174Part008
    + surrogateDiagTailX0RatChunk000Sub000Block174Part009

def surrogateDiagonalTailChunk000Sub000Block174MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block174Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block174Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part010
    + surrogateDiagTailX0RatChunk000Sub000Block174Part011
    + surrogateDiagTailX0RatChunk000Sub000Block174Part012
    + surrogateDiagTailX0RatChunk000Sub000Block174Part013
    + surrogateDiagTailX0RatChunk000Sub000Block174Part014
    + surrogateDiagTailX0RatChunk000Sub000Block174Part015
    + surrogateDiagTailX0RatChunk000Sub000Block174Part016
    + surrogateDiagTailX0RatChunk000Sub000Block174Part017
    + surrogateDiagTailX0RatChunk000Sub000Block174Part018
    + surrogateDiagTailX0RatChunk000Sub000Block174Part019

def surrogateDiagonalTailChunk000Sub000Block174TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block174Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block174Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block174Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part020
    + surrogateDiagTailX0RatChunk000Sub000Block174Part021
    + surrogateDiagTailX0RatChunk000Sub000Block174Part022
    + surrogateDiagTailX0RatChunk000Sub000Block174Part023
    + surrogateDiagTailX0RatChunk000Sub000Block174Part024

def surrogateDiagonalTailChunk000Sub000Block174Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block174HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block174MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block174TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block174 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block174Part000
    + surrogateDiagTailX0RatChunk000Sub000Block174Part001
    + surrogateDiagTailX0RatChunk000Sub000Block174Part002
    + surrogateDiagTailX0RatChunk000Sub000Block174Part003
    + surrogateDiagTailX0RatChunk000Sub000Block174Part004
    + surrogateDiagTailX0RatChunk000Sub000Block174Part005
    + surrogateDiagTailX0RatChunk000Sub000Block174Part006
    + surrogateDiagTailX0RatChunk000Sub000Block174Part007
    + surrogateDiagTailX0RatChunk000Sub000Block174Part008
    + surrogateDiagTailX0RatChunk000Sub000Block174Part009
    + surrogateDiagTailX0RatChunk000Sub000Block174Part010
    + surrogateDiagTailX0RatChunk000Sub000Block174Part011
    + surrogateDiagTailX0RatChunk000Sub000Block174Part012
    + surrogateDiagTailX0RatChunk000Sub000Block174Part013
    + surrogateDiagTailX0RatChunk000Sub000Block174Part014
    + surrogateDiagTailX0RatChunk000Sub000Block174Part015
    + surrogateDiagTailX0RatChunk000Sub000Block174Part016
    + surrogateDiagTailX0RatChunk000Sub000Block174Part017
    + surrogateDiagTailX0RatChunk000Sub000Block174Part018
    + surrogateDiagTailX0RatChunk000Sub000Block174Part019
    + surrogateDiagTailX0RatChunk000Sub000Block174Part020
    + surrogateDiagTailX0RatChunk000Sub000Block174Part021
    + surrogateDiagTailX0RatChunk000Sub000Block174Part022
    + surrogateDiagTailX0RatChunk000Sub000Block174Part023
    + surrogateDiagTailX0RatChunk000Sub000Block174Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block174_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block174Head + surrogateDiagTailX0RatChunk000Sub000Block174Mid + surrogateDiagTailX0RatChunk000Sub000Block174Tail =
      surrogateDiagTailX0RatChunk000Sub000Block174 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block174Head surrogateDiagTailX0RatChunk000Sub000Block174Mid surrogateDiagTailX0RatChunk000Sub000Block174Tail surrogateDiagTailX0RatChunk000Sub000Block174
  ring

def SurrogateDiagonalTailChunk000Sub000Block174HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block174HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block174Head

def SurrogateDiagonalTailChunk000Sub000Block174MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block174MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block174Mid

def SurrogateDiagonalTailChunk000Sub000Block174TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block174TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block174Tail

theorem surrogateDiagonalTailChunk000Sub000Block174_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block174HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block174MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block174TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block174Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block174 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block174HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block174MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block174TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block174Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block174_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
