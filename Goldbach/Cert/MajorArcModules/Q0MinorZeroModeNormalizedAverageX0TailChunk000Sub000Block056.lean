import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [56,57). -/

/- Block 056 covers tail-support indices [1400,1425) and q from 2354 to 2393. -/

def TailChunk000Sub000Block056Part000SupportExplicit : Finset ℕ :=
  ([2354] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part000 : ℚ :=
  (1279270563 : ℚ) / 10522745461600

def SurrogateDiagonalTailChunk000Sub000Block056Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2354
    = surrogateDiagTailX0RatChunk000Sub000Block056Part000

theorem surrogateDiagonalTailChunk000Sub000Block056Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part000] using hcert

def TailChunk000Sub000Block056Part001SupportExplicit : Finset ℕ :=
  ([2355] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part001 : ℚ :=
  (398012605975 : ℚ) / 6065759684395008

def SurrogateDiagonalTailChunk000Sub000Block056Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2355
    = surrogateDiagTailX0RatChunk000Sub000Block056Part001

theorem surrogateDiagonalTailChunk000Sub000Block056Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part001] using hcert

def TailChunk000Sub000Block056Part002SupportExplicit : Finset ℕ :=
  ([2357] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part002 : ℚ :=
  (694292238775 : ℚ) / 77042080689310848

def SurrogateDiagonalTailChunk000Sub000Block056Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2357
    = surrogateDiagTailX0RatChunk000Sub000Block056Part002

theorem surrogateDiagonalTailChunk000Sub000Block056Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part002] using hcert

def TailChunk000Sub000Block056Part003SupportExplicit : Finset ℕ :=
  ([2359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part003 : ℚ :=
  (31433533225 : ℚ) / 1529766710083584

def SurrogateDiagonalTailChunk000Sub000Block056Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2359
    = surrogateDiagTailX0RatChunk000Sub000Block056Part003

theorem surrogateDiagonalTailChunk000Sub000Block056Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part003] using hcert

def TailChunk000Sub000Block056Part004SupportExplicit : Finset ℕ :=
  ([2361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part004 : ℚ :=
  (3436825 : ℚ) / 113087969664

def SurrogateDiagonalTailChunk000Sub000Block056Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2361
    = surrogateDiagTailX0RatChunk000Sub000Block056Part004

theorem surrogateDiagonalTailChunk000Sub000Block056Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part004] using hcert

def TailChunk000Sub000Block056Part005SupportExplicit : Finset ℕ :=
  ([2362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part005 : ℚ :=
  (6969620717 : ℚ) / 96958275777600

def SurrogateDiagonalTailChunk000Sub000Block056Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2362
    = surrogateDiagTailX0RatChunk000Sub000Block056Part005

theorem surrogateDiagonalTailChunk000Sub000Block056Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part005] using hcert

def TailChunk000Sub000Block056Part006SupportExplicit : Finset ℕ :=
  ([2363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part006 : ℚ :=
  (163742646325 : ℚ) / 14858095443443712

def SurrogateDiagonalTailChunk000Sub000Block056Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2363
    = surrogateDiagTailX0RatChunk000Sub000Block056Part006

theorem surrogateDiagonalTailChunk000Sub000Block056Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part006] using hcert

def TailChunk000Sub000Block056Part007SupportExplicit : Finset ℕ :=
  ([2365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part007 : ℚ :=
  (317372207 : ℚ) / 12646880870400

def SurrogateDiagonalTailChunk000Sub000Block056Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2365
    = surrogateDiagTailX0RatChunk000Sub000Block056Part007

theorem surrogateDiagonalTailChunk000Sub000Block056Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part007] using hcert

def TailChunk000Sub000Block056Part008SupportExplicit : Finset ℕ :=
  ([2369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part008 : ℚ :=
  (666286125475 : ℚ) / 63404235329643648

def SurrogateDiagonalTailChunk000Sub000Block056Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2369
    = surrogateDiagTailX0RatChunk000Sub000Block056Part008

theorem surrogateDiagonalTailChunk000Sub000Block056Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part008] using hcert

def TailChunk000Sub000Block056Part009SupportExplicit : Finset ℕ :=
  ([2370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part009 : ℚ :=
  (52529129125 : ℚ) / 94777495068672

def SurrogateDiagonalTailChunk000Sub000Block056Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2370
    = surrogateDiagTailX0RatChunk000Sub000Block056Part009

theorem surrogateDiagonalTailChunk000Sub000Block056Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part009] using hcert

def TailChunk000Sub000Block056Part010SupportExplicit : Finset ℕ :=
  ([2371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part010 : ℚ :=
  (28102583359 : ℚ) / 3155587552312200

def SurrogateDiagonalTailChunk000Sub000Block056Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2371
    = surrogateDiagTailX0RatChunk000Sub000Block056Part010

theorem surrogateDiagonalTailChunk000Sub000Block056Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part010] using hcert

def TailChunk000Sub000Block056Part011SupportExplicit : Finset ℕ :=
  ([2373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part011 : ℚ :=
  (480425 : ℚ) / 9710862336

def SurrogateDiagonalTailChunk000Sub000Block056Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2373
    = surrogateDiagTailX0RatChunk000Sub000Block056Part011

theorem surrogateDiagonalTailChunk000Sub000Block056Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part011] using hcert

def TailChunk000Sub000Block056Part012SupportExplicit : Finset ℕ :=
  ([2374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part012 : ℚ :=
  (176015452325 : ℚ) / 2473635012096804

def SurrogateDiagonalTailChunk000Sub000Block056Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2374
    = surrogateDiagTailX0RatChunk000Sub000Block056Part012

theorem surrogateDiagonalTailChunk000Sub000Block056Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part012] using hcert

def TailChunk000Sub000Block056Part013SupportExplicit : Finset ℕ :=
  ([2377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part013 : ℚ :=
  (706124871775 : ℚ) / 79691610588530688

def SurrogateDiagonalTailChunk000Sub000Block056Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2377
    = surrogateDiagTailX0RatChunk000Sub000Block056Part013

theorem surrogateDiagonalTailChunk000Sub000Block056Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part013] using hcert

def TailChunk000Sub000Block056Part014SupportExplicit : Finset ℕ :=
  ([2378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part014 : ℚ :=
  (13359701767 : ℚ) / 157383406387200

def SurrogateDiagonalTailChunk000Sub000Block056Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2378
    = surrogateDiagTailX0RatChunk000Sub000Block056Part014

theorem surrogateDiagonalTailChunk000Sub000Block056Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part014] using hcert

def TailChunk000Sub000Block056Part015SupportExplicit : Finset ℕ :=
  ([2379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part015 : ℚ :=
  (17209663507 : ℚ) / 430067692339200

def SurrogateDiagonalTailChunk000Sub000Block056Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2379
    = surrogateDiagTailX0RatChunk000Sub000Block056Part015

theorem surrogateDiagonalTailChunk000Sub000Block056Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part015] using hcert

def TailChunk000Sub000Block056Part016SupportExplicit : Finset ℕ :=
  ([2381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part016 : ℚ :=
  (17007483 : ℚ) / 1284187452800

def SurrogateDiagonalTailChunk000Sub000Block056Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2381
    = surrogateDiagTailX0RatChunk000Sub000Block056Part016

theorem surrogateDiagonalTailChunk000Sub000Block056Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part016] using hcert

def TailChunk000Sub000Block056Part017SupportExplicit : Finset ℕ :=
  ([2382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part017 : ℚ :=
  (275098504825 : ℚ) / 983847044302848

def SurrogateDiagonalTailChunk000Sub000Block056Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2382
    = surrogateDiagTailX0RatChunk000Sub000Block056Part017

theorem surrogateDiagonalTailChunk000Sub000Block056Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part017] using hcert

def TailChunk000Sub000Block056Part018SupportExplicit : Finset ℕ :=
  ([2383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part018 : ℚ :=
  (709694157775 : ℚ) / 80499630601218888

def SurrogateDiagonalTailChunk000Sub000Block056Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2383
    = surrogateDiagTailX0RatChunk000Sub000Block056Part018

theorem surrogateDiagonalTailChunk000Sub000Block056Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part018] using hcert

def TailChunk000Sub000Block056Part019SupportExplicit : Finset ℕ :=
  ([2386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part019 : ℚ :=
  (177799381325 : ℚ) / 2524072846746624

def SurrogateDiagonalTailChunk000Sub000Block056Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2386
    = surrogateDiagTailX0RatChunk000Sub000Block056Part019

theorem surrogateDiagonalTailChunk000Sub000Block056Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part019] using hcert

def TailChunk000Sub000Block056Part020SupportExplicit : Finset ℕ :=
  ([2387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part020 : ℚ :=
  (480361553 : ℚ) / 23332665600000

def SurrogateDiagonalTailChunk000Sub000Block056Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2387
    = surrogateDiagTailX0RatChunk000Sub000Block056Part020

theorem surrogateDiagonalTailChunk000Sub000Block056Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part020] using hcert

def TailChunk000Sub000Block056Part021SupportExplicit : Finset ℕ :=
  ([2389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part021 : ℚ :=
  (713272441975 : ℚ) / 81313779683875968

def SurrogateDiagonalTailChunk000Sub000Block056Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2389
    = surrogateDiagTailX0RatChunk000Sub000Block056Part021

theorem surrogateDiagonalTailChunk000Sub000Block056Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part021] using hcert

def TailChunk000Sub000Block056Part022SupportExplicit : Finset ℕ :=
  ([2390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part022 : ℚ :=
  (35565361625 : ℚ) / 256734755563776

def SurrogateDiagonalTailChunk000Sub000Block056Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2390
    = surrogateDiagTailX0RatChunk000Sub000Block056Part022

theorem surrogateDiagonalTailChunk000Sub000Block056Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part022] using hcert

def TailChunk000Sub000Block056Part023SupportExplicit : Finset ℕ :=
  ([2391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part023 : ℚ :=
  (95167275 : ℚ) / 3211753883648

def SurrogateDiagonalTailChunk000Sub000Block056Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2391
    = surrogateDiagTailX0RatChunk000Sub000Block056Part023

theorem surrogateDiagonalTailChunk000Sub000Block056Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part023] using hcert

def TailChunk000Sub000Block056Part024SupportExplicit : Finset ℕ :=
  ([2393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block056Part024 : ℚ :=
  (357759901275 : ℚ) / 27286655347234816

def SurrogateDiagonalTailChunk000Sub000Block056Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 2393
    = surrogateDiagTailX0RatChunk000Sub000Block056Part024

theorem surrogateDiagonalTailChunk000Sub000Block056Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block056Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block056Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block056Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block056Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block056Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block056HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block056Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block056Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block056Part000
    + surrogateDiagTailX0RatChunk000Sub000Block056Part001
    + surrogateDiagTailX0RatChunk000Sub000Block056Part002
    + surrogateDiagTailX0RatChunk000Sub000Block056Part003
    + surrogateDiagTailX0RatChunk000Sub000Block056Part004
    + surrogateDiagTailX0RatChunk000Sub000Block056Part005
    + surrogateDiagTailX0RatChunk000Sub000Block056Part006
    + surrogateDiagTailX0RatChunk000Sub000Block056Part007
    + surrogateDiagTailX0RatChunk000Sub000Block056Part008
    + surrogateDiagTailX0RatChunk000Sub000Block056Part009

def surrogateDiagonalTailChunk000Sub000Block056MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block056Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block056Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block056Part010
    + surrogateDiagTailX0RatChunk000Sub000Block056Part011
    + surrogateDiagTailX0RatChunk000Sub000Block056Part012
    + surrogateDiagTailX0RatChunk000Sub000Block056Part013
    + surrogateDiagTailX0RatChunk000Sub000Block056Part014
    + surrogateDiagTailX0RatChunk000Sub000Block056Part015
    + surrogateDiagTailX0RatChunk000Sub000Block056Part016
    + surrogateDiagTailX0RatChunk000Sub000Block056Part017
    + surrogateDiagTailX0RatChunk000Sub000Block056Part018
    + surrogateDiagTailX0RatChunk000Sub000Block056Part019

def surrogateDiagonalTailChunk000Sub000Block056TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block056Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block056Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block056Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block056Part020
    + surrogateDiagTailX0RatChunk000Sub000Block056Part021
    + surrogateDiagTailX0RatChunk000Sub000Block056Part022
    + surrogateDiagTailX0RatChunk000Sub000Block056Part023
    + surrogateDiagTailX0RatChunk000Sub000Block056Part024

def surrogateDiagonalTailChunk000Sub000Block056Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block056HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block056MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block056TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block056 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block056Part000
    + surrogateDiagTailX0RatChunk000Sub000Block056Part001
    + surrogateDiagTailX0RatChunk000Sub000Block056Part002
    + surrogateDiagTailX0RatChunk000Sub000Block056Part003
    + surrogateDiagTailX0RatChunk000Sub000Block056Part004
    + surrogateDiagTailX0RatChunk000Sub000Block056Part005
    + surrogateDiagTailX0RatChunk000Sub000Block056Part006
    + surrogateDiagTailX0RatChunk000Sub000Block056Part007
    + surrogateDiagTailX0RatChunk000Sub000Block056Part008
    + surrogateDiagTailX0RatChunk000Sub000Block056Part009
    + surrogateDiagTailX0RatChunk000Sub000Block056Part010
    + surrogateDiagTailX0RatChunk000Sub000Block056Part011
    + surrogateDiagTailX0RatChunk000Sub000Block056Part012
    + surrogateDiagTailX0RatChunk000Sub000Block056Part013
    + surrogateDiagTailX0RatChunk000Sub000Block056Part014
    + surrogateDiagTailX0RatChunk000Sub000Block056Part015
    + surrogateDiagTailX0RatChunk000Sub000Block056Part016
    + surrogateDiagTailX0RatChunk000Sub000Block056Part017
    + surrogateDiagTailX0RatChunk000Sub000Block056Part018
    + surrogateDiagTailX0RatChunk000Sub000Block056Part019
    + surrogateDiagTailX0RatChunk000Sub000Block056Part020
    + surrogateDiagTailX0RatChunk000Sub000Block056Part021
    + surrogateDiagTailX0RatChunk000Sub000Block056Part022
    + surrogateDiagTailX0RatChunk000Sub000Block056Part023
    + surrogateDiagTailX0RatChunk000Sub000Block056Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block056_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block056Head + surrogateDiagTailX0RatChunk000Sub000Block056Mid + surrogateDiagTailX0RatChunk000Sub000Block056Tail =
      surrogateDiagTailX0RatChunk000Sub000Block056 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block056Head surrogateDiagTailX0RatChunk000Sub000Block056Mid surrogateDiagTailX0RatChunk000Sub000Block056Tail surrogateDiagTailX0RatChunk000Sub000Block056
  ring

def SurrogateDiagonalTailChunk000Sub000Block056HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block056HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block056Head

def SurrogateDiagonalTailChunk000Sub000Block056MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block056MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block056Mid

def SurrogateDiagonalTailChunk000Sub000Block056TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block056TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block056Tail

theorem surrogateDiagonalTailChunk000Sub000Block056_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block056HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block056MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block056TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block056Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block056 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block056HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block056MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block056TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block056Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block056_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
