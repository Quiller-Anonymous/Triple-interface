import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [79,80). -/

/- Block 079 covers tail-support indices [1975,2000) and q from 3298 to 3335. -/

def TailChunk000Sub000Block079Part000SupportExplicit : Finset ℕ :=
  ([3298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part000 : ℚ :=
  (475634122375 : ℚ) / 13918477177847808

def SurrogateDiagonalTailChunk000Sub000Block079Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3298
    = surrogateDiagTailX0RatChunk000Sub000Block079Part000

theorem surrogateDiagonalTailChunk000Sub000Block079Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part000] using hcert

def TailChunk000Sub000Block079Part001SupportExplicit : Finset ℕ :=
  ([3299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part001 : ℚ :=
  (1360153039975 : ℚ) / 295821315568667208

def SurrogateDiagonalTailChunk000Sub000Block079Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3299
    = surrogateDiagTailX0RatChunk000Sub000Block079Part001

theorem surrogateDiagonalTailChunk000Sub000Block079Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part001] using hcert

def TailChunk000Sub000Block079Part002SupportExplicit : Finset ℕ :=
  ([3301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part002 : ℚ :=
  (10896601 : ℚ) / 4744632736800

def SurrogateDiagonalTailChunk000Sub000Block079Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3301
    = surrogateDiagTailX0RatChunk000Sub000Block079Part002

theorem surrogateDiagonalTailChunk000Sub000Block079Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part002] using hcert

def TailChunk000Sub000Block079Part003SupportExplicit : Finset ℕ :=
  ([3302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part003 : ℚ :=
  (234095434625 : ℚ) / 6534374599517184

def SurrogateDiagonalTailChunk000Sub000Block079Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3302
    = surrogateDiagTailX0RatChunk000Sub000Block079Part003

theorem surrogateDiagonalTailChunk000Sub000Block079Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part003] using hcert

def TailChunk000Sub000Block079Part004SupportExplicit : Finset ℕ :=
  ([3305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part004 : ℚ :=
  (8003969153 : ℚ) / 1619501307494400

def SurrogateDiagonalTailChunk000Sub000Block079Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3305
    = surrogateDiagTailX0RatChunk000Sub000Block079Part004

theorem surrogateDiagonalTailChunk000Sub000Block079Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part004] using hcert

def TailChunk000Sub000Block079Part005SupportExplicit : Finset ℕ :=
  ([3306] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part005 : ℚ :=
  (312634638175 : ℚ) / 2581481323266048

def SurrogateDiagonalTailChunk000Sub000Block079Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3306
    = surrogateDiagTailX0RatChunk000Sub000Block079Part005

theorem surrogateDiagonalTailChunk000Sub000Block079Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part005] using hcert

def TailChunk000Sub000Block079Part006SupportExplicit : Finset ℕ :=
  ([3307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part006 : ℚ :=
  (170878890625 : ℚ) / 74675521550696562

def SurrogateDiagonalTailChunk000Sub000Block079Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3307
    = surrogateDiagTailX0RatChunk000Sub000Block079Part006

theorem surrogateDiagonalTailChunk000Sub000Block079Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part006] using hcert

def TailChunk000Sub000Block079Part007SupportExplicit : Finset ℕ :=
  ([3309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part007 : ℚ :=
  (532017615175 : ℚ) / 59002881225241728

def SurrogateDiagonalTailChunk000Sub000Block079Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3309
    = surrogateDiagTailX0RatChunk000Sub000Block079Part007

theorem surrogateDiagonalTailChunk000Sub000Block079Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part007] using hcert

def TailChunk000Sub000Block079Part008SupportExplicit : Finset ℕ :=
  ([3310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part008 : ℚ :=
  (1638816697 : ℚ) / 30365649515520

def SurrogateDiagonalTailChunk000Sub000Block079Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3310
    = surrogateDiagTailX0RatChunk000Sub000Block079Part008

theorem surrogateDiagonalTailChunk000Sub000Block079Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part008] using hcert

def TailChunk000Sub000Block079Part009SupportExplicit : Finset ℕ :=
  ([3311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part009 : ℚ :=
  (365217001 : ℚ) / 63024446368800

def SurrogateDiagonalTailChunk000Sub000Block079Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3311
    = surrogateDiagTailX0RatChunk000Sub000Block079Part009

theorem surrogateDiagonalTailChunk000Sub000Block079Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part009] using hcert

def TailChunk000Sub000Block079Part010SupportExplicit : Finset ℕ :=
  ([3313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part010 : ℚ :=
  (1371721725775 : ℚ) / 300876432729735168

def SurrogateDiagonalTailChunk000Sub000Block079Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3313
    = surrogateDiagTailX0RatChunk000Sub000Block079Part010

theorem surrogateDiagonalTailChunk000Sub000Block079Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part010] using hcert

def TailChunk000Sub000Block079Part011SupportExplicit : Finset ℕ :=
  ([3314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part011 : ℚ :=
  (57178140425 : ℚ) / 2089419671734272

def SurrogateDiagonalTailChunk000Sub000Block079Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3314
    = surrogateDiagTailX0RatChunk000Sub000Block079Part011

theorem surrogateDiagonalTailChunk000Sub000Block079Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part011] using hcert

def TailChunk000Sub000Block079Part012SupportExplicit : Finset ℕ :=
  ([3315] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part012 : ℚ :=
  (90662053225 : ℚ) / 2319746196307968

def SurrogateDiagonalTailChunk000Sub000Block079Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3315
    = surrogateDiagTailX0RatChunk000Sub000Block079Part012

theorem surrogateDiagonalTailChunk000Sub000Block079Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part012] using hcert

def TailChunk000Sub000Block079Part013SupportExplicit : Finset ℕ :=
  ([3317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part013 : ℚ :=
  (10440984509 : ℚ) / 2045621717735040

def SurrogateDiagonalTailChunk000Sub000Block079Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3317
    = surrogateDiagTailX0RatChunk000Sub000Block079Part013

theorem surrogateDiagonalTailChunk000Sub000Block079Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part013] using hcert

def TailChunk000Sub000Block079Part014SupportExplicit : Finset ℕ :=
  ([3318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part014 : ℚ :=
  (19411375 : ℚ) / 127924033536

def SurrogateDiagonalTailChunk000Sub000Block079Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3318
    = surrogateDiagTailX0RatChunk000Sub000Block079Part014

theorem surrogateDiagonalTailChunk000Sub000Block079Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part014] using hcert

def TailChunk000Sub000Block079Part015SupportExplicit : Finset ℕ :=
  ([3319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part015 : ℚ :=
  (1376694730975 : ℚ) / 303062628524063688

def SurrogateDiagonalTailChunk000Sub000Block079Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3319
    = surrogateDiagTailX0RatChunk000Sub000Block079Part015

theorem surrogateDiagonalTailChunk000Sub000Block079Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part015] using hcert

def TailChunk000Sub000Block079Part016SupportExplicit : Finset ℕ :=
  ([3322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part016 : ℚ :=
  (373810547 : ℚ) / 10127025000000

def SurrogateDiagonalTailChunk000Sub000Block079Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3322
    = surrogateDiagTailX0RatChunk000Sub000Block079Part016

theorem surrogateDiagonalTailChunk000Sub000Block079Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part016] using hcert

def TailChunk000Sub000Block079Part017SupportExplicit : Finset ℕ :=
  ([3323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part017 : ℚ :=
  (172536390625 : ℚ) / 76131674132578482

def SurrogateDiagonalTailChunk000Sub000Block079Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3323
    = surrogateDiagTailX0RatChunk000Sub000Block079Part017

theorem surrogateDiagonalTailChunk000Sub000Block079Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part017] using hcert

def TailChunk000Sub000Block079Part018SupportExplicit : Finset ℕ :=
  ([3326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part018 : ℚ :=
  (57592974425 : ℚ) / 2119866087199752

def SurrogateDiagonalTailChunk000Sub000Block079Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3326
    = surrogateDiagTailX0RatChunk000Sub000Block079Part018

theorem surrogateDiagonalTailChunk000Sub000Block079Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part018] using hcert

def TailChunk000Sub000Block079Part019SupportExplicit : Finset ℕ :=
  ([3327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part019 : ℚ :=
  (614518022275 : ℚ) / 60298413147015168

def SurrogateDiagonalTailChunk000Sub000Block079Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3327
    = surrogateDiagTailX0RatChunk000Sub000Block079Part019

theorem surrogateDiagonalTailChunk000Sub000Block079Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part019] using hcert

def TailChunk000Sub000Block079Part020SupportExplicit : Finset ℕ :=
  ([3329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part020 : ℚ :=
  (173160015625 : ℚ) / 76683184158277632

def SurrogateDiagonalTailChunk000Sub000Block079Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3329
    = surrogateDiagTailX0RatChunk000Sub000Block079Part020

theorem surrogateDiagonalTailChunk000Sub000Block079Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part020] using hcert

def TailChunk000Sub000Block079Part021SupportExplicit : Finset ℕ :=
  ([3331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part021 : ℚ :=
  (277389025 : ℚ) / 122988295950642

def SurrogateDiagonalTailChunk000Sub000Block079Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3331
    = surrogateDiagTailX0RatChunk000Sub000Block079Part021

theorem surrogateDiagonalTailChunk000Sub000Block079Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part021] using hcert

def TailChunk000Sub000Block079Part022SupportExplicit : Finset ℕ :=
  ([3333] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part022 : ℚ :=
  (40054163 : ℚ) / 3200640000000

def SurrogateDiagonalTailChunk000Sub000Block079Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3333
    = surrogateDiagTailX0RatChunk000Sub000Block079Part022

theorem surrogateDiagonalTailChunk000Sub000Block079Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part022] using hcert

def TailChunk000Sub000Block079Part023SupportExplicit : Finset ℕ :=
  ([3334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part023 : ℚ :=
  (125025 : ℚ) / 4624076296

def SurrogateDiagonalTailChunk000Sub000Block079Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3334
    = surrogateDiagTailX0RatChunk000Sub000Block079Part023

theorem surrogateDiagonalTailChunk000Sub000Block079Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part023] using hcert

def TailChunk000Sub000Block079Part024SupportExplicit : Finset ℕ :=
  ([3335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block079Part024 : ℚ :=
  (959469535825 : ℚ) / 92170018116599808

def SurrogateDiagonalTailChunk000Sub000Block079Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3335
    = surrogateDiagTailX0RatChunk000Sub000Block079Part024

theorem surrogateDiagonalTailChunk000Sub000Block079Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block079Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block079Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block079Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block079Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block079Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block079HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block079Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block079Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block079Part000
    + surrogateDiagTailX0RatChunk000Sub000Block079Part001
    + surrogateDiagTailX0RatChunk000Sub000Block079Part002
    + surrogateDiagTailX0RatChunk000Sub000Block079Part003
    + surrogateDiagTailX0RatChunk000Sub000Block079Part004
    + surrogateDiagTailX0RatChunk000Sub000Block079Part005
    + surrogateDiagTailX0RatChunk000Sub000Block079Part006
    + surrogateDiagTailX0RatChunk000Sub000Block079Part007
    + surrogateDiagTailX0RatChunk000Sub000Block079Part008
    + surrogateDiagTailX0RatChunk000Sub000Block079Part009

def surrogateDiagonalTailChunk000Sub000Block079MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block079Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block079Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block079Part010
    + surrogateDiagTailX0RatChunk000Sub000Block079Part011
    + surrogateDiagTailX0RatChunk000Sub000Block079Part012
    + surrogateDiagTailX0RatChunk000Sub000Block079Part013
    + surrogateDiagTailX0RatChunk000Sub000Block079Part014
    + surrogateDiagTailX0RatChunk000Sub000Block079Part015
    + surrogateDiagTailX0RatChunk000Sub000Block079Part016
    + surrogateDiagTailX0RatChunk000Sub000Block079Part017
    + surrogateDiagTailX0RatChunk000Sub000Block079Part018
    + surrogateDiagTailX0RatChunk000Sub000Block079Part019

def surrogateDiagonalTailChunk000Sub000Block079TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block079Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block079Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block079Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block079Part020
    + surrogateDiagTailX0RatChunk000Sub000Block079Part021
    + surrogateDiagTailX0RatChunk000Sub000Block079Part022
    + surrogateDiagTailX0RatChunk000Sub000Block079Part023
    + surrogateDiagTailX0RatChunk000Sub000Block079Part024

def surrogateDiagonalTailChunk000Sub000Block079Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block079HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block079MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block079TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block079 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block079Part000
    + surrogateDiagTailX0RatChunk000Sub000Block079Part001
    + surrogateDiagTailX0RatChunk000Sub000Block079Part002
    + surrogateDiagTailX0RatChunk000Sub000Block079Part003
    + surrogateDiagTailX0RatChunk000Sub000Block079Part004
    + surrogateDiagTailX0RatChunk000Sub000Block079Part005
    + surrogateDiagTailX0RatChunk000Sub000Block079Part006
    + surrogateDiagTailX0RatChunk000Sub000Block079Part007
    + surrogateDiagTailX0RatChunk000Sub000Block079Part008
    + surrogateDiagTailX0RatChunk000Sub000Block079Part009
    + surrogateDiagTailX0RatChunk000Sub000Block079Part010
    + surrogateDiagTailX0RatChunk000Sub000Block079Part011
    + surrogateDiagTailX0RatChunk000Sub000Block079Part012
    + surrogateDiagTailX0RatChunk000Sub000Block079Part013
    + surrogateDiagTailX0RatChunk000Sub000Block079Part014
    + surrogateDiagTailX0RatChunk000Sub000Block079Part015
    + surrogateDiagTailX0RatChunk000Sub000Block079Part016
    + surrogateDiagTailX0RatChunk000Sub000Block079Part017
    + surrogateDiagTailX0RatChunk000Sub000Block079Part018
    + surrogateDiagTailX0RatChunk000Sub000Block079Part019
    + surrogateDiagTailX0RatChunk000Sub000Block079Part020
    + surrogateDiagTailX0RatChunk000Sub000Block079Part021
    + surrogateDiagTailX0RatChunk000Sub000Block079Part022
    + surrogateDiagTailX0RatChunk000Sub000Block079Part023
    + surrogateDiagTailX0RatChunk000Sub000Block079Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block079_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block079Head + surrogateDiagTailX0RatChunk000Sub000Block079Mid + surrogateDiagTailX0RatChunk000Sub000Block079Tail =
      surrogateDiagTailX0RatChunk000Sub000Block079 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block079Head surrogateDiagTailX0RatChunk000Sub000Block079Mid surrogateDiagTailX0RatChunk000Sub000Block079Tail surrogateDiagTailX0RatChunk000Sub000Block079
  ring

def SurrogateDiagonalTailChunk000Sub000Block079HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block079HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block079Head

def SurrogateDiagonalTailChunk000Sub000Block079MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block079MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block079Mid

def SurrogateDiagonalTailChunk000Sub000Block079TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block079TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block079Tail

theorem surrogateDiagonalTailChunk000Sub000Block079_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block079HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block079MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block079TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block079Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block079 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block079HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block079MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block079TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block079Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block079_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
