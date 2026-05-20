import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [76,77). -/

/- Block 076 covers tail-support indices [1900,1925) and q from 3170 to 3214. -/

def TailChunk000Sub000Block076Part000SupportExplicit : Finset ℕ :=
  ([3170] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part000 : ℚ :=
  (127341096375 : ℚ) / 2127619195764736

def SurrogateDiagonalTailChunk000Sub000Block076Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3170
    = surrogateDiagTailX0RatChunk000Sub000Block076Part000

theorem surrogateDiagonalTailChunk000Sub000Block076Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part000] using hcert

def TailChunk000Sub000Block076Part001SupportExplicit : Finset ℕ :=
  ([3171] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part001 : ℚ :=
  (4710278057 : ℚ) / 209993990400000

def SurrogateDiagonalTailChunk000Sub000Block076Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3171
    = surrogateDiagTailX0RatChunk000Sub000Block076Part001

theorem surrogateDiagonalTailChunk000Sub000Block076Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part001] using hcert

def TailChunk000Sub000Block076Part002SupportExplicit : Finset ℕ :=
  ([3173] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part002 : ℚ :=
  (1168303669075 : ℚ) / 199319244089482368

def SurrogateDiagonalTailChunk000Sub000Block076Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3173
    = surrogateDiagTailX0RatChunk000Sub000Block076Part002

theorem surrogateDiagonalTailChunk000Sub000Block076Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part002] using hcert

def TailChunk000Sub000Block076Part003SupportExplicit : Finset ℕ :=
  ([3178] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part003 : ℚ :=
  (203681539625 : ℚ) / 4227032834639424

def SurrogateDiagonalTailChunk000Sub000Block076Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3178
    = surrogateDiagTailX0RatChunk000Sub000Block076Part003

theorem surrogateDiagonalTailChunk000Sub000Block076Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part003] using hcert

def TailChunk000Sub000Block076Part004SupportExplicit : Finset ℕ :=
  ([3181] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part004 : ℚ :=
  (252969025 : ℚ) / 102281085886752

def SurrogateDiagonalTailChunk000Sub000Block076Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3181
    = surrogateDiagTailX0RatChunk000Sub000Block076Part004

theorem surrogateDiagonalTailChunk000Sub000Block076Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part004] using hcert

def TailChunk000Sub000Block076Part005SupportExplicit : Finset ℕ :=
  ([3182] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part005 : ℚ :=
  (1395985025 : ℚ) / 40335645676032

def SurrogateDiagonalTailChunk000Sub000Block076Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3182
    = surrogateDiagTailX0RatChunk000Sub000Block076Part005

theorem surrogateDiagonalTailChunk000Sub000Block076Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part005] using hcert

def TailChunk000Sub000Block076Part006SupportExplicit : Finset ℕ :=
  ([3183] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part006 : ℚ :=
  (19691362237 : ℚ) / 2020367128627200

def SurrogateDiagonalTailChunk000Sub000Block076Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3183
    = surrogateDiagTailX0RatChunk000Sub000Block076Part006

theorem surrogateDiagonalTailChunk000Sub000Block076Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part006] using hcert

def TailChunk000Sub000Block076Part007SupportExplicit : Finset ℕ :=
  ([3187] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part007 : ℚ :=
  (1269367200775 : ℚ) / 257638015187617608

def SurrogateDiagonalTailChunk000Sub000Block076Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3187
    = surrogateDiagTailX0RatChunk000Sub000Block076Part007

theorem surrogateDiagonalTailChunk000Sub000Block076Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part007] using hcert

def TailChunk000Sub000Block076Part008SupportExplicit : Finset ℕ :=
  ([3189] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part008 : ℚ :=
  (776158266325 : ℚ) / 50891459790146688

def SurrogateDiagonalTailChunk000Sub000Block076Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3189
    = surrogateDiagTailX0RatChunk000Sub000Block076Part008

theorem surrogateDiagonalTailChunk000Sub000Block076Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part008] using hcert

def TailChunk000Sub000Block076Part009SupportExplicit : Finset ℕ :=
  ([3190] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part009 : ℚ :=
  (2731909169 : ℚ) / 31476681277440

def SurrogateDiagonalTailChunk000Sub000Block076Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3190
    = surrogateDiagTailX0RatChunk000Sub000Block076Part009

theorem surrogateDiagonalTailChunk000Sub000Block076Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part009] using hcert

def TailChunk000Sub000Block076Part010SupportExplicit : Finset ℕ :=
  ([3191] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part010 : ℚ :=
  (50902222519 : ℚ) / 10357372181224200

def SurrogateDiagonalTailChunk000Sub000Block076Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3191
    = surrogateDiagTailX0RatChunk000Sub000Block076Part010

theorem surrogateDiagonalTailChunk000Sub000Block076Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part010] using hcert

def TailChunk000Sub000Block076Part011SupportExplicit : Finset ℕ :=
  ([3193] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part011 : ℚ :=
  (1792326581 : ℚ) / 324794593929600

def SurrogateDiagonalTailChunk000Sub000Block076Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3193
    = surrogateDiagTailX0RatChunk000Sub000Block076Part011

theorem surrogateDiagonalTailChunk000Sub000Block076Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part011] using hcert

def TailChunk000Sub000Block076Part012SupportExplicit : Finset ℕ :=
  ([3194] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part012 : ℚ :=
  (1083923825 : ℚ) / 36789155399808

def SurrogateDiagonalTailChunk000Sub000Block076Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3194
    = surrogateDiagTailX0RatChunk000Sub000Block076Part012

theorem surrogateDiagonalTailChunk000Sub000Block076Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part012] using hcert

def TailChunk000Sub000Block076Part013SupportExplicit : Finset ℕ :=
  ([3197] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part013 : ℚ :=
  (1927947875 : ℚ) / 655675441826592

def SurrogateDiagonalTailChunk000Sub000Block076Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3197
    = surrogateDiagTailX0RatChunk000Sub000Block076Part013

theorem surrogateDiagonalTailChunk000Sub000Block076Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part013] using hcert

def TailChunk000Sub000Block076Part014SupportExplicit : Finset ℕ :=
  ([3198] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part014 : ℚ :=
  (2889797341 : ℚ) / 21237910732800

def SurrogateDiagonalTailChunk000Sub000Block076Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3198
    = surrogateDiagTailX0RatChunk000Sub000Block076Part014

theorem surrogateDiagonalTailChunk000Sub000Block076Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part014] using hcert

def TailChunk000Sub000Block076Part015SupportExplicit : Finset ℕ :=
  ([3199] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part015 : ℚ :=
  (9371341675 : ℚ) / 2189330145833472

def SurrogateDiagonalTailChunk000Sub000Block076Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3199
    = surrogateDiagTailX0RatChunk000Sub000Block076Part015

theorem surrogateDiagonalTailChunk000Sub000Block076Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part015] using hcert

def TailChunk000Sub000Block076Part016SupportExplicit : Finset ℕ :=
  ([3201] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part016 : ℚ :=
  (1304444791 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block076Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3201
    = surrogateDiagTailX0RatChunk000Sub000Block076Part016

theorem surrogateDiagonalTailChunk000Sub000Block076Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part016] using hcert

def TailChunk000Sub000Block076Part017SupportExplicit : Finset ℕ :=
  ([3202] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part017 : ℚ :=
  (6405439299 : ℚ) / 218497024000000

def SurrogateDiagonalTailChunk000Sub000Block076Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3202
    = surrogateDiagTailX0RatChunk000Sub000Block076Part017

theorem surrogateDiagonalTailChunk000Sub000Block076Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part017] using hcert

def TailChunk000Sub000Block076Part018SupportExplicit : Finset ℕ :=
  ([3203] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part018 : ℚ :=
  (160300140625 : ℚ) / 65713133662742802

def SurrogateDiagonalTailChunk000Sub000Block076Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3203
    = surrogateDiagTailX0RatChunk000Sub000Block076Part018

theorem surrogateDiagonalTailChunk000Sub000Block076Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part018] using hcert

def TailChunk000Sub000Block076Part019SupportExplicit : Finset ℕ :=
  ([3205] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part019 : ℚ :=
  (22581673699 : ℚ) / 4295826289459200

def SurrogateDiagonalTailChunk000Sub000Block076Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3205
    = surrogateDiagTailX0RatChunk000Sub000Block076Part019

theorem surrogateDiagonalTailChunk000Sub000Block076Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part019] using hcert

def TailChunk000Sub000Block076Part020SupportExplicit : Finset ℕ :=
  ([3206] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part020 : ℚ :=
  (29349125075 : ℚ) / 486517810185216

def SurrogateDiagonalTailChunk000Sub000Block076Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3206
    = surrogateDiagTailX0RatChunk000Sub000Block076Part020

theorem surrogateDiagonalTailChunk000Sub000Block076Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part020] using hcert

def TailChunk000Sub000Block076Part021SupportExplicit : Finset ℕ :=
  ([3207] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part021 : ℚ :=
  (784946113675 : ℚ) / 52051332559915008

def SurrogateDiagonalTailChunk000Sub000Block076Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3207
    = surrogateDiagTailX0RatChunk000Sub000Block076Part021

theorem surrogateDiagonalTailChunk000Sub000Block076Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part021] using hcert

def TailChunk000Sub000Block076Part022SupportExplicit : Finset ℕ :=
  ([3209] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part022 : ℚ :=
  (1286952682975 : ℚ) / 264828241851598848

def SurrogateDiagonalTailChunk000Sub000Block076Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3209
    = surrogateDiagTailX0RatChunk000Sub000Block076Part022

theorem surrogateDiagonalTailChunk000Sub000Block076Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part022] using hcert

def TailChunk000Sub000Block076Part023SupportExplicit : Finset ℕ :=
  ([3210] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part023 : ℚ :=
  (32356275575 : ℚ) / 161629370290176

def SurrogateDiagonalTailChunk000Sub000Block076Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3210
    = surrogateDiagTailX0RatChunk000Sub000Block076Part023

theorem surrogateDiagonalTailChunk000Sub000Block076Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part023] using hcert

def TailChunk000Sub000Block076Part024SupportExplicit : Finset ℕ :=
  ([3214] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block076Part024 : ℚ :=
  (161338501275 : ℚ) / 5544824029470616

def SurrogateDiagonalTailChunk000Sub000Block076Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3214
    = surrogateDiagTailX0RatChunk000Sub000Block076Part024

theorem surrogateDiagonalTailChunk000Sub000Block076Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block076Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block076Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block076Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block076Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block076Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block076HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block076Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block076Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block076Part000
    + surrogateDiagTailX0RatChunk000Sub000Block076Part001
    + surrogateDiagTailX0RatChunk000Sub000Block076Part002
    + surrogateDiagTailX0RatChunk000Sub000Block076Part003
    + surrogateDiagTailX0RatChunk000Sub000Block076Part004
    + surrogateDiagTailX0RatChunk000Sub000Block076Part005
    + surrogateDiagTailX0RatChunk000Sub000Block076Part006
    + surrogateDiagTailX0RatChunk000Sub000Block076Part007
    + surrogateDiagTailX0RatChunk000Sub000Block076Part008
    + surrogateDiagTailX0RatChunk000Sub000Block076Part009

def surrogateDiagonalTailChunk000Sub000Block076MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block076Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block076Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block076Part010
    + surrogateDiagTailX0RatChunk000Sub000Block076Part011
    + surrogateDiagTailX0RatChunk000Sub000Block076Part012
    + surrogateDiagTailX0RatChunk000Sub000Block076Part013
    + surrogateDiagTailX0RatChunk000Sub000Block076Part014
    + surrogateDiagTailX0RatChunk000Sub000Block076Part015
    + surrogateDiagTailX0RatChunk000Sub000Block076Part016
    + surrogateDiagTailX0RatChunk000Sub000Block076Part017
    + surrogateDiagTailX0RatChunk000Sub000Block076Part018
    + surrogateDiagTailX0RatChunk000Sub000Block076Part019

def surrogateDiagonalTailChunk000Sub000Block076TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block076Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block076Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block076Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block076Part020
    + surrogateDiagTailX0RatChunk000Sub000Block076Part021
    + surrogateDiagTailX0RatChunk000Sub000Block076Part022
    + surrogateDiagTailX0RatChunk000Sub000Block076Part023
    + surrogateDiagTailX0RatChunk000Sub000Block076Part024

def surrogateDiagonalTailChunk000Sub000Block076Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block076HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block076MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block076TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block076 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block076Part000
    + surrogateDiagTailX0RatChunk000Sub000Block076Part001
    + surrogateDiagTailX0RatChunk000Sub000Block076Part002
    + surrogateDiagTailX0RatChunk000Sub000Block076Part003
    + surrogateDiagTailX0RatChunk000Sub000Block076Part004
    + surrogateDiagTailX0RatChunk000Sub000Block076Part005
    + surrogateDiagTailX0RatChunk000Sub000Block076Part006
    + surrogateDiagTailX0RatChunk000Sub000Block076Part007
    + surrogateDiagTailX0RatChunk000Sub000Block076Part008
    + surrogateDiagTailX0RatChunk000Sub000Block076Part009
    + surrogateDiagTailX0RatChunk000Sub000Block076Part010
    + surrogateDiagTailX0RatChunk000Sub000Block076Part011
    + surrogateDiagTailX0RatChunk000Sub000Block076Part012
    + surrogateDiagTailX0RatChunk000Sub000Block076Part013
    + surrogateDiagTailX0RatChunk000Sub000Block076Part014
    + surrogateDiagTailX0RatChunk000Sub000Block076Part015
    + surrogateDiagTailX0RatChunk000Sub000Block076Part016
    + surrogateDiagTailX0RatChunk000Sub000Block076Part017
    + surrogateDiagTailX0RatChunk000Sub000Block076Part018
    + surrogateDiagTailX0RatChunk000Sub000Block076Part019
    + surrogateDiagTailX0RatChunk000Sub000Block076Part020
    + surrogateDiagTailX0RatChunk000Sub000Block076Part021
    + surrogateDiagTailX0RatChunk000Sub000Block076Part022
    + surrogateDiagTailX0RatChunk000Sub000Block076Part023
    + surrogateDiagTailX0RatChunk000Sub000Block076Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block076_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block076Head + surrogateDiagTailX0RatChunk000Sub000Block076Mid + surrogateDiagTailX0RatChunk000Sub000Block076Tail =
      surrogateDiagTailX0RatChunk000Sub000Block076 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block076Head surrogateDiagTailX0RatChunk000Sub000Block076Mid surrogateDiagTailX0RatChunk000Sub000Block076Tail surrogateDiagTailX0RatChunk000Sub000Block076
  ring

def SurrogateDiagonalTailChunk000Sub000Block076HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block076HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block076Head

def SurrogateDiagonalTailChunk000Sub000Block076MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block076MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block076Mid

def SurrogateDiagonalTailChunk000Sub000Block076TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block076TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block076Tail

theorem surrogateDiagonalTailChunk000Sub000Block076_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block076HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block076MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block076TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block076Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block076 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block076HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block076MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block076TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block076Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block076_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
