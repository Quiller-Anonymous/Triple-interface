import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [151,152). -/

/- Block 151 covers tail-support indices [3775,3800) and q from 6262 to 6299. -/

def TailChunk000Sub000Block151Part000SupportExplicit : Finset ℕ :=
  ([6262] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part000 : ℚ :=
  (5822287163 : ℚ) / 1012702500000000

def SurrogateDiagonalTailChunk000Sub000Block151Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6262
    = surrogateDiagTailX0RatChunk000Sub000Block151Part000

theorem surrogateDiagonalTailChunk000Sub000Block151Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part000] using hcert

def TailChunk000Sub000Block151Part001SupportExplicit : Finset ℕ :=
  ([6263] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part001 : ℚ :=
  (612893265625 : ℚ) / 961211859850393842

def SurrogateDiagonalTailChunk000Sub000Block151Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6263
    = surrogateDiagTailX0RatChunk000Sub000Block151Part001

theorem surrogateDiagonalTailChunk000Sub000Block151Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part001] using hcert

def TailChunk000Sub000Block151Part002SupportExplicit : Finset ℕ :=
  ([6265] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part002 : ℚ :=
  (1558293527575 : ℚ) / 832821320958640128

def SurrogateDiagonalTailChunk000Sub000Block151Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6265
    = surrogateDiagTailX0RatChunk000Sub000Block151Part002

theorem surrogateDiagonalTailChunk000Sub000Block151Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part002] using hcert

def TailChunk000Sub000Block151Part003SupportExplicit : Finset ℕ :=
  ([6266] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part003 : ℚ :=
  (22182761387 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub000Block151Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6266
    = surrogateDiagTailX0RatChunk000Sub000Block151Part003

theorem surrogateDiagonalTailChunk000Sub000Block151Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part003] using hcert

def TailChunk000Sub000Block151Part004SupportExplicit : Finset ℕ :=
  ([6267] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part004 : ℚ :=
  (681631436225 : ℚ) / 380223384381702144

def SurrogateDiagonalTailChunk000Sub000Block151Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6267
    = surrogateDiagTailX0RatChunk000Sub000Block151Part004

theorem surrogateDiagonalTailChunk000Sub000Block151Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part004] using hcert

def TailChunk000Sub000Block151Part005SupportExplicit : Finset ℕ :=
  ([6269] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part005 : ℚ :=
  (614068140625 : ℚ) / 964901138298691872

def SurrogateDiagonalTailChunk000Sub000Block151Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6269
    = surrogateDiagTailX0RatChunk000Sub000Block151Part005

theorem surrogateDiagonalTailChunk000Sub000Block151Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part005] using hcert

def TailChunk000Sub000Block151Part006SupportExplicit : Finset ℕ :=
  ([6270] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part006 : ℚ :=
  (3283589009 : ℚ) / 71677948723200

def SurrogateDiagonalTailChunk000Sub000Block151Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6270
    = surrogateDiagTailX0RatChunk000Sub000Block151Part006

theorem surrogateDiagonalTailChunk000Sub000Block151Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part006] using hcert

def TailChunk000Sub000Block151Part007SupportExplicit : Finset ℕ :=
  ([6271] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part007 : ℚ :=
  (983136025 : ℚ) / 1545813207231282

def SurrogateDiagonalTailChunk000Sub000Block151Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6271
    = surrogateDiagTailX0RatChunk000Sub000Block151Part007

theorem surrogateDiagonalTailChunk000Sub000Block151Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part007] using hcert

def TailChunk000Sub000Block151Part008SupportExplicit : Finset ℕ :=
  ([6274] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part008 : ℚ :=
  (153762015625 : ℚ) / 60460409397706752

def SurrogateDiagonalTailChunk000Sub000Block151Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6274
    = surrogateDiagTailX0RatChunk000Sub000Block151Part008

theorem surrogateDiagonalTailChunk000Sub000Block151Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part008] using hcert

def TailChunk000Sub000Block151Part009SupportExplicit : Finset ℕ :=
  ([6277] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part009 : ℚ :=
  (615636390625 : ℚ) / 969836683930435872

def SurrogateDiagonalTailChunk000Sub000Block151Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6277
    = surrogateDiagTailX0RatChunk000Sub000Block151Part009

theorem surrogateDiagonalTailChunk000Sub000Block151Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part009] using hcert

def TailChunk000Sub000Block151Part010SupportExplicit : Finset ℕ :=
  ([6278] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part010 : ℚ :=
  (151603079125 : ℚ) / 52274996796137472

def SurrogateDiagonalTailChunk000Sub000Block151Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6278
    = surrogateDiagTailX0RatChunk000Sub000Block151Part010

theorem surrogateDiagonalTailChunk000Sub000Block151Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part010] using hcert

def TailChunk000Sub000Block151Part011SupportExplicit : Finset ℕ :=
  ([6279] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part011 : ℚ :=
  (1162820890525 : ℚ) / 251864843341529088

def SurrogateDiagonalTailChunk000Sub000Block151Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6279
    = surrogateDiagTailX0RatChunk000Sub000Block151Part011

theorem surrogateDiagonalTailChunk000Sub000Block151Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part011] using hcert

def TailChunk000Sub000Block151Part012SupportExplicit : Finset ℕ :=
  ([6281] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part012 : ℚ :=
  (87864767047 : ℚ) / 105581122002000000

def SurrogateDiagonalTailChunk000Sub000Block151Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6281
    = surrogateDiagTailX0RatChunk000Sub000Block151Part012

theorem surrogateDiagonalTailChunk000Sub000Block151Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part012] using hcert

def TailChunk000Sub000Block151Part013SupportExplicit : Finset ℕ :=
  ([6283] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part013 : ℚ :=
  (1328026039 : ℚ) / 1948767563577600

def SurrogateDiagonalTailChunk000Sub000Block151Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6283
    = surrogateDiagTailX0RatChunk000Sub000Block151Part013

theorem surrogateDiagonalTailChunk000Sub000Block151Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part013] using hcert

def TailChunk000Sub000Block151Part014SupportExplicit : Finset ℕ :=
  ([6285] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part014 : ℚ :=
  (623825489525 : ℚ) / 156337059180724224

def SurrogateDiagonalTailChunk000Sub000Block151Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6285
    = surrogateDiagTailX0RatChunk000Sub000Block151Part014

theorem surrogateDiagonalTailChunk000Sub000Block151Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part014] using hcert

def TailChunk000Sub000Block151Part015SupportExplicit : Finset ℕ :=
  ([6286] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part015 : ℚ :=
  (18092848625 : ℚ) / 4079377893556224

def SurrogateDiagonalTailChunk000Sub000Block151Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6286
    = surrogateDiagTailX0RatChunk000Sub000Block151Part015

theorem surrogateDiagonalTailChunk000Sub000Block151Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part015] using hcert

def TailChunk000Sub000Block151Part016SupportExplicit : Finset ℕ :=
  ([6287] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part016 : ℚ :=
  (617599515625 : ℚ) / 976032713965301202

def SurrogateDiagonalTailChunk000Sub000Block151Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6287
    = surrogateDiagTailX0RatChunk000Sub000Block151Part016

theorem surrogateDiagonalTailChunk000Sub000Block151Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part016] using hcert

def TailChunk000Sub000Block151Part017SupportExplicit : Finset ℕ :=
  ([6289] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part017 : ℚ :=
  (4193731687 : ℚ) / 5659915524753600

def SurrogateDiagonalTailChunk000Sub000Block151Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6289
    = surrogateDiagTailX0RatChunk000Sub000Block151Part017

theorem surrogateDiagonalTailChunk000Sub000Block151Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part017] using hcert

def TailChunk000Sub000Block151Part018SupportExplicit : Finset ℕ :=
  ([6290] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part018 : ℚ :=
  (94242463175 : ℚ) / 7829143412539392

def SurrogateDiagonalTailChunk000Sub000Block151Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6290
    = surrogateDiagTailX0RatChunk000Sub000Block151Part018

theorem surrogateDiagonalTailChunk000Sub000Block151Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part018] using hcert

def TailChunk000Sub000Block151Part019SupportExplicit : Finset ℕ :=
  ([6293] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part019 : ℚ :=
  (829242781 : ℚ) / 717078145351680

def SurrogateDiagonalTailChunk000Sub000Block151Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6293
    = surrogateDiagTailX0RatChunk000Sub000Block151Part019

theorem surrogateDiagonalTailChunk000Sub000Block151Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part019] using hcert

def TailChunk000Sub000Block151Part020SupportExplicit : Finset ℕ :=
  ([6294] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part020 : ℚ :=
  (755845824175 : ℚ) / 48260517230051328

def SurrogateDiagonalTailChunk000Sub000Block151Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6294
    = surrogateDiagTailX0RatChunk000Sub000Block151Part020

theorem surrogateDiagonalTailChunk000Sub000Block151Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part020] using hcert

def TailChunk000Sub000Block151Part021SupportExplicit : Finset ℕ :=
  ([6295] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part021 : ℚ :=
  (117556311475 : ℚ) / 100200388634352768

def SurrogateDiagonalTailChunk000Sub000Block151Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6295
    = surrogateDiagTailX0RatChunk000Sub000Block151Part021

theorem surrogateDiagonalTailChunk000Sub000Block151Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part021] using hcert

def TailChunk000Sub000Block151Part022SupportExplicit : Finset ℕ :=
  ([6297] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part022 : ℚ :=
  (43010819225 : ℚ) / 24222490745463204

def SurrogateDiagonalTailChunk000Sub000Block151Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6297
    = surrogateDiagTailX0RatChunk000Sub000Block151Part022

theorem surrogateDiagonalTailChunk000Sub000Block151Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part022] using hcert

def TailChunk000Sub000Block151Part023SupportExplicit : Finset ℕ :=
  ([6298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part023 : ℚ :=
  (107846179775 : ℚ) / 19312622104710528

def SurrogateDiagonalTailChunk000Sub000Block151Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6298
    = surrogateDiagTailX0RatChunk000Sub000Block151Part023

theorem surrogateDiagonalTailChunk000Sub000Block151Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part023] using hcert

def TailChunk000Sub000Block151Part024SupportExplicit : Finset ℕ :=
  ([6299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block151Part024 : ℚ :=
  (619959390625 : ℚ) / 983507084808554802

def SurrogateDiagonalTailChunk000Sub000Block151Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6299
    = surrogateDiagTailX0RatChunk000Sub000Block151Part024

theorem surrogateDiagonalTailChunk000Sub000Block151Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block151Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block151Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block151Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block151Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block151Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block151Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block151HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block151Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block151Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block151Part000
    + surrogateDiagTailX0RatChunk000Sub000Block151Part001
    + surrogateDiagTailX0RatChunk000Sub000Block151Part002
    + surrogateDiagTailX0RatChunk000Sub000Block151Part003
    + surrogateDiagTailX0RatChunk000Sub000Block151Part004
    + surrogateDiagTailX0RatChunk000Sub000Block151Part005
    + surrogateDiagTailX0RatChunk000Sub000Block151Part006
    + surrogateDiagTailX0RatChunk000Sub000Block151Part007
    + surrogateDiagTailX0RatChunk000Sub000Block151Part008
    + surrogateDiagTailX0RatChunk000Sub000Block151Part009

def surrogateDiagonalTailChunk000Sub000Block151MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block151Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block151Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block151Part010
    + surrogateDiagTailX0RatChunk000Sub000Block151Part011
    + surrogateDiagTailX0RatChunk000Sub000Block151Part012
    + surrogateDiagTailX0RatChunk000Sub000Block151Part013
    + surrogateDiagTailX0RatChunk000Sub000Block151Part014
    + surrogateDiagTailX0RatChunk000Sub000Block151Part015
    + surrogateDiagTailX0RatChunk000Sub000Block151Part016
    + surrogateDiagTailX0RatChunk000Sub000Block151Part017
    + surrogateDiagTailX0RatChunk000Sub000Block151Part018
    + surrogateDiagTailX0RatChunk000Sub000Block151Part019

def surrogateDiagonalTailChunk000Sub000Block151TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block151Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block151Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block151Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block151Part020
    + surrogateDiagTailX0RatChunk000Sub000Block151Part021
    + surrogateDiagTailX0RatChunk000Sub000Block151Part022
    + surrogateDiagTailX0RatChunk000Sub000Block151Part023
    + surrogateDiagTailX0RatChunk000Sub000Block151Part024

def surrogateDiagonalTailChunk000Sub000Block151Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block151HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block151MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block151TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block151 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block151Part000
    + surrogateDiagTailX0RatChunk000Sub000Block151Part001
    + surrogateDiagTailX0RatChunk000Sub000Block151Part002
    + surrogateDiagTailX0RatChunk000Sub000Block151Part003
    + surrogateDiagTailX0RatChunk000Sub000Block151Part004
    + surrogateDiagTailX0RatChunk000Sub000Block151Part005
    + surrogateDiagTailX0RatChunk000Sub000Block151Part006
    + surrogateDiagTailX0RatChunk000Sub000Block151Part007
    + surrogateDiagTailX0RatChunk000Sub000Block151Part008
    + surrogateDiagTailX0RatChunk000Sub000Block151Part009
    + surrogateDiagTailX0RatChunk000Sub000Block151Part010
    + surrogateDiagTailX0RatChunk000Sub000Block151Part011
    + surrogateDiagTailX0RatChunk000Sub000Block151Part012
    + surrogateDiagTailX0RatChunk000Sub000Block151Part013
    + surrogateDiagTailX0RatChunk000Sub000Block151Part014
    + surrogateDiagTailX0RatChunk000Sub000Block151Part015
    + surrogateDiagTailX0RatChunk000Sub000Block151Part016
    + surrogateDiagTailX0RatChunk000Sub000Block151Part017
    + surrogateDiagTailX0RatChunk000Sub000Block151Part018
    + surrogateDiagTailX0RatChunk000Sub000Block151Part019
    + surrogateDiagTailX0RatChunk000Sub000Block151Part020
    + surrogateDiagTailX0RatChunk000Sub000Block151Part021
    + surrogateDiagTailX0RatChunk000Sub000Block151Part022
    + surrogateDiagTailX0RatChunk000Sub000Block151Part023
    + surrogateDiagTailX0RatChunk000Sub000Block151Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block151_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block151Head + surrogateDiagTailX0RatChunk000Sub000Block151Mid + surrogateDiagTailX0RatChunk000Sub000Block151Tail =
      surrogateDiagTailX0RatChunk000Sub000Block151 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block151Head surrogateDiagTailX0RatChunk000Sub000Block151Mid surrogateDiagTailX0RatChunk000Sub000Block151Tail surrogateDiagTailX0RatChunk000Sub000Block151
  ring

def SurrogateDiagonalTailChunk000Sub000Block151HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block151HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block151Head

def SurrogateDiagonalTailChunk000Sub000Block151MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block151MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block151Mid

def SurrogateDiagonalTailChunk000Sub000Block151TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block151TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block151Tail

theorem surrogateDiagonalTailChunk000Sub000Block151_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block151HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block151MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block151TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block151Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block151 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block151HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block151MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block151TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block151Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block151_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
