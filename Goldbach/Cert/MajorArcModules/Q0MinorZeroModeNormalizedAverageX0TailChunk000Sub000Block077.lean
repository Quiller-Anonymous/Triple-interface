import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [77,78). -/

/- Block 077 covers tail-support indices [1925,1950) and q from 3215 to 3255. -/

def TailChunk000Sub000Block077Part000SupportExplicit : Finset ℕ :=
  ([3215] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part000 : ℚ :=
  (980313608575 : ℚ) / 108744408786290688

def SurrogateDiagonalTailChunk000Sub000Block077Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3215
    = surrogateDiagTailX0RatChunk000Sub000Block077Part000

theorem surrogateDiagonalTailChunk000Sub000Block077Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part000] using hcert

def TailChunk000Sub000Block077Part001SupportExplicit : Finset ℕ :=
  ([3217] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part001 : ℚ :=
  (161704515625 : ℚ) / 66869954525601792

def SurrogateDiagonalTailChunk000Sub000Block077Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3217
    = surrogateDiagTailX0RatChunk000Sub000Block077Part001

theorem surrogateDiagonalTailChunk000Sub000Block077Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part001] using hcert

def TailChunk000Sub000Block077Part002SupportExplicit : Finset ℕ :=
  ([3218] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part002 : ℚ :=
  (53913446825 : ℚ) / 1857498736822272

def SurrogateDiagonalTailChunk000Sub000Block077Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3218
    = surrogateDiagTailX0RatChunk000Sub000Block077Part002

theorem surrogateDiagonalTailChunk000Sub000Block077Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part002] using hcert

def TailChunk000Sub000Block077Part003SupportExplicit : Finset ℕ :=
  ([3219] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part003 : ℚ :=
  (273154771325 : ℚ) / 20651850586128384

def SurrogateDiagonalTailChunk000Sub000Block077Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3219
    = surrogateDiagTailX0RatChunk000Sub000Block077Part003

theorem surrogateDiagonalTailChunk000Sub000Block077Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part003] using hcert

def TailChunk000Sub000Block077Part004SupportExplicit : Finset ℕ :=
  ([3221] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part004 : ℚ :=
  (259371025 : ℚ) / 107525219303712

def SurrogateDiagonalTailChunk000Sub000Block077Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3221
    = surrogateDiagTailX0RatChunk000Sub000Block077Part004

theorem surrogateDiagonalTailChunk000Sub000Block077Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part004] using hcert

def TailChunk000Sub000Block077Part005SupportExplicit : Finset ℕ :=
  ([3223] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part005 : ℚ :=
  (4970960591 : ℚ) / 1454280737187840

def SurrogateDiagonalTailChunk000Sub000Block077Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3223
    = surrogateDiagTailX0RatChunk000Sub000Block077Part005

theorem surrogateDiagonalTailChunk000Sub000Block077Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part005] using hcert

def TailChunk000Sub000Block077Part006SupportExplicit : Finset ℕ :=
  ([3226] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part006 : ℚ :=
  (325025992325 : ℚ) / 8442226757649984

def SurrogateDiagonalTailChunk000Sub000Block077Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3226
    = surrogateDiagTailX0RatChunk000Sub000Block077Part006

theorem surrogateDiagonalTailChunk000Sub000Block077Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part006] using hcert

def TailChunk000Sub000Block077Part007SupportExplicit : Finset ℕ :=
  ([3227] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part007 : ℚ :=
  (4770155473 : ℚ) / 644882614732800

def SurrogateDiagonalTailChunk000Sub000Block077Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3227
    = surrogateDiagTailX0RatChunk000Sub000Block077Part007

theorem surrogateDiagonalTailChunk000Sub000Block077Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part007] using hcert

def TailChunk000Sub000Block077Part008SupportExplicit : Finset ℕ :=
  ([3229] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part008 : ℚ :=
  (1303044463975 : ℚ) / 271494454433920128

def SurrogateDiagonalTailChunk000Sub000Block077Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3229
    = surrogateDiagTailX0RatChunk000Sub000Block077Part008

theorem surrogateDiagonalTailChunk000Sub000Block077Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part008] using hcert

def TailChunk000Sub000Block077Part009SupportExplicit : Finset ℕ :=
  ([3230] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part009 : ℚ :=
  (118394495725 : ℚ) / 1467964389851136

def SurrogateDiagonalTailChunk000Sub000Block077Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3230
    = surrogateDiagTailX0RatChunk000Sub000Block077Part009

theorem surrogateDiagonalTailChunk000Sub000Block077Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part009] using hcert

def TailChunk000Sub000Block077Part010SupportExplicit : Finset ℕ :=
  ([3233] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part010 : ℚ :=
  (50041729099 : ℚ) / 9477749506867200

def SurrogateDiagonalTailChunk000Sub000Block077Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3233
    = surrogateDiagTailX0RatChunk000Sub000Block077Part010

theorem surrogateDiagonalTailChunk000Sub000Block077Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part010] using hcert

def TailChunk000Sub000Block077Part011SupportExplicit : Finset ℕ :=
  ([3235] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part011 : ℚ :=
  (330850599525 : ℚ) / 37159994535417856

def SurrogateDiagonalTailChunk000Sub000Block077Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3235
    = surrogateDiagTailX0RatChunk000Sub000Block077Part011

theorem surrogateDiagonalTailChunk000Sub000Block077Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part011] using hcert

def TailChunk000Sub000Block077Part012SupportExplicit : Finset ℕ :=
  ([3237] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part012 : ℚ :=
  (59917030775 : ℚ) / 3125690618241024

def SurrogateDiagonalTailChunk000Sub000Block077Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3237
    = surrogateDiagTailX0RatChunk000Sub000Block077Part012

theorem surrogateDiagonalTailChunk000Sub000Block077Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part012] using hcert

def TailChunk000Sub000Block077Part013SupportExplicit : Finset ℕ :=
  ([3238] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part013 : ℚ :=
  (163757033475 : ℚ) / 5712413979158296

def SurrogateDiagonalTailChunk000Sub000Block077Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3238
    = surrogateDiagTailX0RatChunk000Sub000Block077Part013

theorem surrogateDiagonalTailChunk000Sub000Block077Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part013] using hcert

def TailChunk000Sub000Block077Part014SupportExplicit : Finset ℕ :=
  ([3239] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part014 : ℚ :=
  (6444676363 : ℚ) / 2369437376716800

def SurrogateDiagonalTailChunk000Sub000Block077Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3239
    = surrogateDiagTailX0RatChunk000Sub000Block077Part014

theorem surrogateDiagonalTailChunk000Sub000Block077Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part014] using hcert

def TailChunk000Sub000Block077Part015SupportExplicit : Finset ℕ :=
  ([3241] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part015 : ℚ :=
  (153900858025 : ℚ) / 36909636771424032

def SurrogateDiagonalTailChunk000Sub000Block077Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3241
    = surrogateDiagTailX0RatChunk000Sub000Block077Part015

theorem surrogateDiagonalTailChunk000Sub000Block077Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part015] using hcert

def TailChunk000Sub000Block077Part016SupportExplicit : Finset ℕ :=
  ([3242] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part016 : ℚ :=
  (2188824953 : ℚ) / 76542809500800

def SurrogateDiagonalTailChunk000Sub000Block077Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3242
    = surrogateDiagTailX0RatChunk000Sub000Block077Part016

theorem surrogateDiagonalTailChunk000Sub000Block077Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part016] using hcert

def TailChunk000Sub000Block077Part017SupportExplicit : Finset ℕ :=
  ([3243] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part017 : ℚ :=
  (552416141275 : ℚ) / 41963228276901888

def SurrogateDiagonalTailChunk000Sub000Block077Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3243
    = surrogateDiagTailX0RatChunk000Sub000Block077Part017

theorem surrogateDiagonalTailChunk000Sub000Block077Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part017] using hcert

def TailChunk000Sub000Block077Part018SupportExplicit : Finset ℕ :=
  ([3245] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part018 : ℚ :=
  (22505530459 : ℚ) / 2897602380595200

def SurrogateDiagonalTailChunk000Sub000Block077Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3245
    = surrogateDiagTailX0RatChunk000Sub000Block077Part018

theorem surrogateDiagonalTailChunk000Sub000Block077Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part018] using hcert

def TailChunk000Sub000Block077Part019SupportExplicit : Finset ℕ :=
  ([3246] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part019 : ℚ :=
  (54779 : ℚ) / 566870400

def SurrogateDiagonalTailChunk000Sub000Block077Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3246
    = surrogateDiagTailX0RatChunk000Sub000Block077Part019

theorem surrogateDiagonalTailChunk000Sub000Block077Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part019] using hcert

def TailChunk000Sub000Block077Part020SupportExplicit : Finset ℕ :=
  ([3247] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part020 : ℚ :=
  (48581130037 : ℚ) / 8542425199411200

def SurrogateDiagonalTailChunk000Sub000Block077Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3247
    = surrogateDiagTailX0RatChunk000Sub000Block077Part020

theorem surrogateDiagonalTailChunk000Sub000Block077Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part020] using hcert

def TailChunk000Sub000Block077Part021SupportExplicit : Finset ℕ :=
  ([3251] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part021 : ℚ :=
  (52834435999 : ℚ) / 11158871953125000

def SurrogateDiagonalTailChunk000Sub000Block077Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3251
    = surrogateDiagTailX0RatChunk000Sub000Block077Part021

theorem surrogateDiagonalTailChunk000Sub000Block077Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part021] using hcert

def TailChunk000Sub000Block077Part022SupportExplicit : Finset ℕ :=
  ([3253] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part022 : ℚ :=
  (1322486574775 : ℚ) / 279659132777467008

def SurrogateDiagonalTailChunk000Sub000Block077Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3253
    = surrogateDiagTailX0RatChunk000Sub000Block077Part022

theorem surrogateDiagonalTailChunk000Sub000Block077Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part022] using hcert

def TailChunk000Sub000Block077Part023SupportExplicit : Finset ℕ :=
  ([3254] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part023 : ℚ :=
  (55126461425 : ℚ) / 1942077310954632

def SurrogateDiagonalTailChunk000Sub000Block077Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3254
    = surrogateDiagTailX0RatChunk000Sub000Block077Part023

theorem surrogateDiagonalTailChunk000Sub000Block077Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part023] using hcert

def TailChunk000Sub000Block077Part024SupportExplicit : Finset ℕ :=
  ([3255] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block077Part024 : ℚ :=
  (9997969301 : ℚ) / 215033846169600

def SurrogateDiagonalTailChunk000Sub000Block077Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3255
    = surrogateDiagTailX0RatChunk000Sub000Block077Part024

theorem surrogateDiagonalTailChunk000Sub000Block077Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block077Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block077Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block077Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block077Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block077Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block077HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block077Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block077Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block077Part000
    + surrogateDiagTailX0RatChunk000Sub000Block077Part001
    + surrogateDiagTailX0RatChunk000Sub000Block077Part002
    + surrogateDiagTailX0RatChunk000Sub000Block077Part003
    + surrogateDiagTailX0RatChunk000Sub000Block077Part004
    + surrogateDiagTailX0RatChunk000Sub000Block077Part005
    + surrogateDiagTailX0RatChunk000Sub000Block077Part006
    + surrogateDiagTailX0RatChunk000Sub000Block077Part007
    + surrogateDiagTailX0RatChunk000Sub000Block077Part008
    + surrogateDiagTailX0RatChunk000Sub000Block077Part009

def surrogateDiagonalTailChunk000Sub000Block077MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block077Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block077Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block077Part010
    + surrogateDiagTailX0RatChunk000Sub000Block077Part011
    + surrogateDiagTailX0RatChunk000Sub000Block077Part012
    + surrogateDiagTailX0RatChunk000Sub000Block077Part013
    + surrogateDiagTailX0RatChunk000Sub000Block077Part014
    + surrogateDiagTailX0RatChunk000Sub000Block077Part015
    + surrogateDiagTailX0RatChunk000Sub000Block077Part016
    + surrogateDiagTailX0RatChunk000Sub000Block077Part017
    + surrogateDiagTailX0RatChunk000Sub000Block077Part018
    + surrogateDiagTailX0RatChunk000Sub000Block077Part019

def surrogateDiagonalTailChunk000Sub000Block077TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block077Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block077Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block077Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block077Part020
    + surrogateDiagTailX0RatChunk000Sub000Block077Part021
    + surrogateDiagTailX0RatChunk000Sub000Block077Part022
    + surrogateDiagTailX0RatChunk000Sub000Block077Part023
    + surrogateDiagTailX0RatChunk000Sub000Block077Part024

def surrogateDiagonalTailChunk000Sub000Block077Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block077HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block077MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block077TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block077 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block077Part000
    + surrogateDiagTailX0RatChunk000Sub000Block077Part001
    + surrogateDiagTailX0RatChunk000Sub000Block077Part002
    + surrogateDiagTailX0RatChunk000Sub000Block077Part003
    + surrogateDiagTailX0RatChunk000Sub000Block077Part004
    + surrogateDiagTailX0RatChunk000Sub000Block077Part005
    + surrogateDiagTailX0RatChunk000Sub000Block077Part006
    + surrogateDiagTailX0RatChunk000Sub000Block077Part007
    + surrogateDiagTailX0RatChunk000Sub000Block077Part008
    + surrogateDiagTailX0RatChunk000Sub000Block077Part009
    + surrogateDiagTailX0RatChunk000Sub000Block077Part010
    + surrogateDiagTailX0RatChunk000Sub000Block077Part011
    + surrogateDiagTailX0RatChunk000Sub000Block077Part012
    + surrogateDiagTailX0RatChunk000Sub000Block077Part013
    + surrogateDiagTailX0RatChunk000Sub000Block077Part014
    + surrogateDiagTailX0RatChunk000Sub000Block077Part015
    + surrogateDiagTailX0RatChunk000Sub000Block077Part016
    + surrogateDiagTailX0RatChunk000Sub000Block077Part017
    + surrogateDiagTailX0RatChunk000Sub000Block077Part018
    + surrogateDiagTailX0RatChunk000Sub000Block077Part019
    + surrogateDiagTailX0RatChunk000Sub000Block077Part020
    + surrogateDiagTailX0RatChunk000Sub000Block077Part021
    + surrogateDiagTailX0RatChunk000Sub000Block077Part022
    + surrogateDiagTailX0RatChunk000Sub000Block077Part023
    + surrogateDiagTailX0RatChunk000Sub000Block077Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block077_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block077Head + surrogateDiagTailX0RatChunk000Sub000Block077Mid + surrogateDiagTailX0RatChunk000Sub000Block077Tail =
      surrogateDiagTailX0RatChunk000Sub000Block077 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block077Head surrogateDiagTailX0RatChunk000Sub000Block077Mid surrogateDiagTailX0RatChunk000Sub000Block077Tail surrogateDiagTailX0RatChunk000Sub000Block077
  ring

def SurrogateDiagonalTailChunk000Sub000Block077HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block077HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block077Head

def SurrogateDiagonalTailChunk000Sub000Block077MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block077MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block077Mid

def SurrogateDiagonalTailChunk000Sub000Block077TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block077TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block077Tail

theorem surrogateDiagonalTailChunk000Sub000Block077_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block077HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block077MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block077TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block077Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block077 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block077HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block077MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block077TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block077Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block077_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
