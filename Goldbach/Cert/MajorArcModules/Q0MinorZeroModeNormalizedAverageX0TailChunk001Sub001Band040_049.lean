import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 001, subchunk 001, blocks [40,50). -/

/-- Block 040 covers tail-support indices [16000,16025) and q from 26371 to 26410. -/

def TailChunk001Sub001Block040Part000SupportExplicit : Finset ℕ :=
  ([26371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part000 : ℚ :=
  (17385741025 : ℚ) / 483645742860220722

def SurrogateDiagonalTailChunk001Sub001Block040Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26371
    = surrogateDiagTailX0RatChunk001Sub001Block040Part000

theorem surrogateDiagonalTailChunk001Sub001Block040Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part000] using hcert

def TailChunk001Sub001Block040Part001SupportExplicit : Finset ℕ :=
  ([26373] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part001 : ℚ :=
  (6181091468025 : ℚ) / 72407645002915741696

def SurrogateDiagonalTailChunk001Sub001Block040Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26373
    = surrogateDiagTailX0RatChunk001Sub001Block040Part001

theorem surrogateDiagonalTailChunk001Sub001Block040Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part001] using hcert

def TailChunk001Sub001Block040Part002SupportExplicit : Finset ℕ :=
  ([26374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part002 : ℚ :=
  (2717140140625 : ℚ) / 18898143968891184402

def SurrogateDiagonalTailChunk001Sub001Block040Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26374
    = surrogateDiagTailX0RatChunk001Sub001Block040Part002

theorem surrogateDiagonalTailChunk001Sub001Block040Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part002] using hcert

def TailChunk001Sub001Block040Part003SupportExplicit : Finset ℕ :=
  ([26377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part003 : ℚ :=
  (37277080117075 : ℚ) / 877048571876654481408

def SurrogateDiagonalTailChunk001Sub001Block040Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26377
    = surrogateDiagTailX0RatChunk001Sub001Block040Part003

theorem surrogateDiagonalTailChunk001Sub001Block040Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part003] using hcert

def TailChunk001Sub001Block040Part004SupportExplicit : Finset ℕ :=
  ([26381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part004 : ℚ :=
  (143846165161 : ℚ) / 3187664423541227520

def SurrogateDiagonalTailChunk001Sub001Block040Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26381
    = surrogateDiagTailX0RatChunk001Sub001Block040Part004

theorem surrogateDiagonalTailChunk001Sub001Block040Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part004] using hcert

def TailChunk001Sub001Block040Part005SupportExplicit : Finset ℕ :=
  ([26382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part005 : ℚ :=
  (4831828560325 : ℚ) / 14940928125461710848

def SurrogateDiagonalTailChunk001Sub001Block040Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26382
    = surrogateDiagTailX0RatChunk001Sub001Block040Part005

theorem surrogateDiagonalTailChunk001Sub001Block040Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part005] using hcert

def TailChunk001Sub001Block040Part006SupportExplicit : Finset ℕ :=
  ([26383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part006 : ℚ :=
  (3549663497125 : ℚ) / 72582667911447478272

def SurrogateDiagonalTailChunk001Sub001Block040Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26383
    = surrogateDiagTailX0RatChunk001Sub001Block040Part006

theorem surrogateDiagonalTailChunk001Sub001Block040Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part006] using hcert

def TailChunk001Sub001Block040Part007SupportExplicit : Finset ℕ :=
  ([26385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part007 : ℚ :=
  (3187437678625 : ℚ) / 24456950157474865152

def SurrogateDiagonalTailChunk001Sub001Block040Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26385
    = surrogateDiagTailX0RatChunk001Sub001Block040Part007

theorem surrogateDiagonalTailChunk001Sub001Block040Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part007] using hcert

def TailChunk001Sub001Block040Part008SupportExplicit : Finset ℕ :=
  ([26386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part008 : ℚ :=
  (10551507881425 : ℚ) / 70280949758514887808

def SurrogateDiagonalTailChunk001Sub001Block040Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26386
    = surrogateDiagTailX0RatChunk001Sub001Block040Part008

theorem surrogateDiagonalTailChunk001Sub001Block040Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part008] using hcert

def TailChunk001Sub001Block040Part009SupportExplicit : Finset ℕ :=
  ([26387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part009 : ℚ :=
  (10879277640625 : ℚ) / 303012887503928914002

def SurrogateDiagonalTailChunk001Sub001Block040Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26387
    = surrogateDiagTailX0RatChunk001Sub001Block040Part009

theorem surrogateDiagonalTailChunk001Sub001Block040Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part009] using hcert

def TailChunk001Sub001Block040Part010SupportExplicit : Finset ℕ :=
  ([26389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part010 : ℚ :=
  (145215929359 : ℚ) / 3307375959244864320

def SurrogateDiagonalTailChunk001Sub001Block040Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26389
    = surrogateDiagTailX0RatChunk001Sub001Block040Part010

theorem surrogateDiagonalTailChunk001Sub001Block040Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part010] using hcert

def TailChunk001Sub001Block040Part011SupportExplicit : Finset ℕ :=
  ([26390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part011 : ℚ :=
  (22026763925 : ℚ) / 48952534722674688

def SurrogateDiagonalTailChunk001Sub001Block040Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26390
    = surrogateDiagTailX0RatChunk001Sub001Block040Part011

theorem surrogateDiagonalTailChunk001Sub001Block040Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part011] using hcert

def TailChunk001Sub001Block040Part012SupportExplicit : Finset ℕ :=
  ([26391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part012 : ℚ :=
  (162532045975 : ℚ) / 1771662565028353536

def SurrogateDiagonalTailChunk001Sub001Block040Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26391
    = surrogateDiagTailX0RatChunk001Sub001Block040Part012

theorem surrogateDiagonalTailChunk001Sub001Block040Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part012] using hcert

def TailChunk001Sub001Block040Part013SupportExplicit : Finset ℕ :=
  ([26393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part013 : ℚ :=
  (10884225765625 : ℚ) / 303288593946281882112

def SurrogateDiagonalTailChunk001Sub001Block040Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26393
    = surrogateDiagTailX0RatChunk001Sub001Block040Part013

theorem surrogateDiagonalTailChunk001Sub001Block040Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part013] using hcert

def TailChunk001Sub001Block040Part014SupportExplicit : Finset ℕ :=
  ([26394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part014 : ℚ :=
  (1542117092025 : ℚ) / 4408535790004043776

def SurrogateDiagonalTailChunk001Sub001Block040Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26394
    = surrogateDiagTailX0RatChunk001Sub001Block040Part014

theorem surrogateDiagonalTailChunk001Sub001Block040Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part014] using hcert

def TailChunk001Sub001Block040Part015SupportExplicit : Finset ℕ :=
  ([26395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part015 : ℚ :=
  (1741158390625 : ℚ) / 31047339100441093248

def SurrogateDiagonalTailChunk001Sub001Block040Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26395
    = surrogateDiagTailX0RatChunk001Sub001Block040Part015

theorem surrogateDiagonalTailChunk001Sub001Block040Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part015] using hcert

def TailChunk001Sub001Block040Part016SupportExplicit : Finset ℕ :=
  ([26398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part016 : ℚ :=
  (167271261275 : ℚ) / 1111440804398217216

def SurrogateDiagonalTailChunk001Sub001Block040Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26398
    = surrogateDiagTailX0RatChunk001Sub001Block040Part016

theorem surrogateDiagonalTailChunk001Sub001Block040Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part016] using hcert

def TailChunk001Sub001Block040Part017SupportExplicit : Finset ℕ :=
  ([26399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part017 : ℚ :=
  (10889175015625 : ℚ) / 303564488491418784402

def SurrogateDiagonalTailChunk001Sub001Block040Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26399
    = surrogateDiagTailX0RatChunk001Sub001Block040Part017

theorem surrogateDiagonalTailChunk001Sub001Block040Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part017] using hcert

def TailChunk001Sub001Block040Part018SupportExplicit : Finset ℕ :=
  ([26401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part018 : ℚ :=
  (2437411294675 : ℚ) / 59422876985425133568

def SurrogateDiagonalTailChunk001Sub001Block040Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26401
    = surrogateDiagTailX0RatChunk001Sub001Block040Part018

theorem surrogateDiagonalTailChunk001Sub001Block040Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part018] using hcert

def TailChunk001Sub001Block040Part019SupportExplicit : Finset ℕ :=
  ([26402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part019 : ℚ :=
  (72399154675 : ℚ) / 473747830665169032

def SurrogateDiagonalTailChunk001Sub001Block040Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26402
    = surrogateDiagTailX0RatChunk001Sub001Block040Part019

theorem surrogateDiagonalTailChunk001Sub001Block040Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part019] using hcert

def TailChunk001Sub001Block040Part020SupportExplicit : Finset ℕ :=
  ([26403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part020 : ℚ :=
  (4178701790875 : ℚ) / 43311040586501455872

def SurrogateDiagonalTailChunk001Sub001Block040Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26403
    = surrogateDiagTailX0RatChunk001Sub001Block040Part020

theorem surrogateDiagonalTailChunk001Sub001Block040Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part020] using hcert

def TailChunk001Sub001Block040Part021SupportExplicit : Finset ℕ :=
  ([26405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part021 : ℚ :=
  (929321675 : ℚ) / 16583693388742656

def SurrogateDiagonalTailChunk001Sub001Block040Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26405
    = surrogateDiagTailX0RatChunk001Sub001Block040Part021

theorem surrogateDiagonalTailChunk001Sub001Block040Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part021] using hcert

def TailChunk001Sub001Block040Part022SupportExplicit : Finset ℕ :=
  ([26407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part022 : ℚ :=
  (10895775765625 : ℚ) / 303932640637109581362

def SurrogateDiagonalTailChunk001Sub001Block040Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26407
    = surrogateDiagTailX0RatChunk001Sub001Block040Part022

theorem surrogateDiagonalTailChunk001Sub001Block040Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part022] using hcert

def TailChunk001Sub001Block040Part023SupportExplicit : Finset ℕ :=
  ([26409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part023 : ℚ :=
  (19369425119725 : ℚ) / 240144308651543372928

def SurrogateDiagonalTailChunk001Sub001Block040Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26409
    = surrogateDiagTailX0RatChunk001Sub001Block040Part023

theorem surrogateDiagonalTailChunk001Sub001Block040Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part023] using hcert

def TailChunk001Sub001Block040Part024SupportExplicit : Finset ℕ :=
  ([26410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block040Part024 : ℚ :=
  (1681490715475 : ℚ) / 6092747762777137152

def SurrogateDiagonalTailChunk001Sub001Block040Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26410
    = surrogateDiagTailX0RatChunk001Sub001Block040Part024

theorem surrogateDiagonalTailChunk001Sub001Block040Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block040Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block040Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block040Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block040Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block040Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block040HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block040Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block040Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block040Part000
    + surrogateDiagTailX0RatChunk001Sub001Block040Part001
    + surrogateDiagTailX0RatChunk001Sub001Block040Part002
    + surrogateDiagTailX0RatChunk001Sub001Block040Part003
    + surrogateDiagTailX0RatChunk001Sub001Block040Part004
    + surrogateDiagTailX0RatChunk001Sub001Block040Part005
    + surrogateDiagTailX0RatChunk001Sub001Block040Part006
    + surrogateDiagTailX0RatChunk001Sub001Block040Part007
    + surrogateDiagTailX0RatChunk001Sub001Block040Part008
    + surrogateDiagTailX0RatChunk001Sub001Block040Part009

def surrogateDiagonalTailChunk001Sub001Block040MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block040Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block040Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block040Part010
    + surrogateDiagTailX0RatChunk001Sub001Block040Part011
    + surrogateDiagTailX0RatChunk001Sub001Block040Part012
    + surrogateDiagTailX0RatChunk001Sub001Block040Part013
    + surrogateDiagTailX0RatChunk001Sub001Block040Part014
    + surrogateDiagTailX0RatChunk001Sub001Block040Part015
    + surrogateDiagTailX0RatChunk001Sub001Block040Part016
    + surrogateDiagTailX0RatChunk001Sub001Block040Part017
    + surrogateDiagTailX0RatChunk001Sub001Block040Part018
    + surrogateDiagTailX0RatChunk001Sub001Block040Part019

def surrogateDiagonalTailChunk001Sub001Block040TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block040Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block040Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block040Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block040Part020
    + surrogateDiagTailX0RatChunk001Sub001Block040Part021
    + surrogateDiagTailX0RatChunk001Sub001Block040Part022
    + surrogateDiagTailX0RatChunk001Sub001Block040Part023
    + surrogateDiagTailX0RatChunk001Sub001Block040Part024

def surrogateDiagonalTailChunk001Sub001Block040Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block040HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block040MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block040TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block040 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block040Part000
    + surrogateDiagTailX0RatChunk001Sub001Block040Part001
    + surrogateDiagTailX0RatChunk001Sub001Block040Part002
    + surrogateDiagTailX0RatChunk001Sub001Block040Part003
    + surrogateDiagTailX0RatChunk001Sub001Block040Part004
    + surrogateDiagTailX0RatChunk001Sub001Block040Part005
    + surrogateDiagTailX0RatChunk001Sub001Block040Part006
    + surrogateDiagTailX0RatChunk001Sub001Block040Part007
    + surrogateDiagTailX0RatChunk001Sub001Block040Part008
    + surrogateDiagTailX0RatChunk001Sub001Block040Part009
    + surrogateDiagTailX0RatChunk001Sub001Block040Part010
    + surrogateDiagTailX0RatChunk001Sub001Block040Part011
    + surrogateDiagTailX0RatChunk001Sub001Block040Part012
    + surrogateDiagTailX0RatChunk001Sub001Block040Part013
    + surrogateDiagTailX0RatChunk001Sub001Block040Part014
    + surrogateDiagTailX0RatChunk001Sub001Block040Part015
    + surrogateDiagTailX0RatChunk001Sub001Block040Part016
    + surrogateDiagTailX0RatChunk001Sub001Block040Part017
    + surrogateDiagTailX0RatChunk001Sub001Block040Part018
    + surrogateDiagTailX0RatChunk001Sub001Block040Part019
    + surrogateDiagTailX0RatChunk001Sub001Block040Part020
    + surrogateDiagTailX0RatChunk001Sub001Block040Part021
    + surrogateDiagTailX0RatChunk001Sub001Block040Part022
    + surrogateDiagTailX0RatChunk001Sub001Block040Part023
    + surrogateDiagTailX0RatChunk001Sub001Block040Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block040_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block040Head + surrogateDiagTailX0RatChunk001Sub001Block040Mid + surrogateDiagTailX0RatChunk001Sub001Block040Tail =
      surrogateDiagTailX0RatChunk001Sub001Block040 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block040Head surrogateDiagTailX0RatChunk001Sub001Block040Mid surrogateDiagTailX0RatChunk001Sub001Block040Tail surrogateDiagTailX0RatChunk001Sub001Block040
  ring

def SurrogateDiagonalTailChunk001Sub001Block040HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block040HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block040Head

def SurrogateDiagonalTailChunk001Sub001Block040MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block040MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block040Mid

def SurrogateDiagonalTailChunk001Sub001Block040TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block040TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block040Tail

theorem surrogateDiagonalTailChunk001Sub001Block040_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block040HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block040MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block040TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block040Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block040 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block040HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block040MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block040TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block040Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block040_eq_head_add_mid_add_tail

/-- Block 041 covers tail-support indices [16025,16050) and q from 26413 to 26453. -/

def TailChunk001Sub001Block041Part000SupportExplicit : Finset ℕ :=
  ([26413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part000 : ℚ :=
  (93644526031 : ℚ) / 2508154781722214400

def SurrogateDiagonalTailChunk001Sub001Block041Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26413
    = surrogateDiagTailX0RatChunk001Sub001Block041Part000

theorem surrogateDiagonalTailChunk001Sub001Block041Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part000] using hcert

def TailChunk001Sub001Block041Part001SupportExplicit : Finset ℕ :=
  ([26414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part001 : ℚ :=
  (418686014017 : ℚ) / 2752645614175027200

def SurrogateDiagonalTailChunk001Sub001Block041Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26414
    = surrogateDiagTailX0RatChunk001Sub001Block041Part001

theorem surrogateDiagonalTailChunk001Sub001Block041Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part001] using hcert

def TailChunk001Sub001Block041Part002SupportExplicit : Finset ℕ :=
  ([26417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part002 : ℚ :=
  (10904029515625 : ℚ) / 304393301598999355392

def SurrogateDiagonalTailChunk001Sub001Block041Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26417
    = surrogateDiagTailX0RatChunk001Sub001Block041Part002

theorem surrogateDiagonalTailChunk001Sub001Block041Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part002] using hcert

def TailChunk001Sub001Block041Part003SupportExplicit : Finset ℕ :=
  ([26418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part003 : ℚ :=
  (1142257398025 : ℚ) / 1902481849247072256

def SurrogateDiagonalTailChunk001Sub001Block041Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26418
    = surrogateDiagTailX0RatChunk001Sub001Block041Part003

theorem surrogateDiagonalTailChunk001Sub001Block041Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part003] using hcert

def TailChunk001Sub001Block041Part004SupportExplicit : Finset ℕ :=
  ([26419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part004 : ℚ :=
  (408470359579 : ℚ) / 10539610307665420800

def SurrogateDiagonalTailChunk001Sub001Block041Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26419
    = surrogateDiagTailX0RatChunk001Sub001Block041Part004

theorem surrogateDiagonalTailChunk001Sub001Block041Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part004] using hcert

def TailChunk001Sub001Block041Part005SupportExplicit : Finset ℕ :=
  ([26421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part005 : ℚ :=
  (19387033119325 : ℚ) / 240581133111080995968

def SurrogateDiagonalTailChunk001Sub001Block041Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26421
    = surrogateDiagTailX0RatChunk001Sub001Block041Part005

theorem surrogateDiagonalTailChunk001Sub001Block041Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part005] using hcert

def TailChunk001Sub001Block041Part006SupportExplicit : Finset ℕ :=
  ([26422] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part006 : ℚ :=
  (123654579089 : ℚ) / 691338240000000000

def SurrogateDiagonalTailChunk001Sub001Block041Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26422
    = surrogateDiagTailX0RatChunk001Sub001Block041Part006

theorem surrogateDiagonalTailChunk001Sub001Block041Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part006] using hcert

def TailChunk001Sub001Block041Part007SupportExplicit : Finset ℕ :=
  ([26423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part007 : ℚ :=
  (10908983265625 : ℚ) / 304669949410835472882

def SurrogateDiagonalTailChunk001Sub001Block041Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26423
    = surrogateDiagTailX0RatChunk001Sub001Block041Part007

theorem surrogateDiagonalTailChunk001Sub001Block041Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part007] using hcert

def TailChunk001Sub001Block041Part008SupportExplicit : Finset ℕ :=
  ([26426] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part008 : ℚ :=
  (84604541351 : ℚ) / 564334825887498240

def SurrogateDiagonalTailChunk001Sub001Block041Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26426
    = surrogateDiagTailX0RatChunk001Sub001Block041Part008

theorem surrogateDiagonalTailChunk001Sub001Block041Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part008] using hcert

def TailChunk001Sub001Block041Part009SupportExplicit : Finset ℕ :=
  ([26427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part009 : ℚ :=
  (270627497325 : ℚ) / 3023758351902204928

def SurrogateDiagonalTailChunk001Sub001Block041Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26427
    = surrogateDiagTailX0RatChunk001Sub001Block041Part009

theorem surrogateDiagonalTailChunk001Sub001Block041Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part009] using hcert

def TailChunk001Sub001Block041Part010SupportExplicit : Finset ℕ :=
  ([26429] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part010 : ℚ :=
  (16808503016525 : ℚ) / 343585896705525694464

def SurrogateDiagonalTailChunk001Sub001Block041Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26429
    = surrogateDiagTailX0RatChunk001Sub001Block041Part010

theorem surrogateDiagonalTailChunk001Sub001Block041Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part010] using hcert

def TailChunk001Sub001Block041Part011SupportExplicit : Finset ℕ :=
  ([26430] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part011 : ℚ :=
  (9298721811 : ℚ) / 16378956433326080

def SurrogateDiagonalTailChunk001Sub001Block041Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26430
    = surrogateDiagTailX0RatChunk001Sub001Block041Part011

theorem surrogateDiagonalTailChunk001Sub001Block041Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part011] using hcert

def TailChunk001Sub001Block041Part012SupportExplicit : Finset ℕ :=
  ([26431] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part012 : ℚ :=
  (17464944025 : ℚ) / 488062570311473202

def SurrogateDiagonalTailChunk001Sub001Block041Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26431
    = surrogateDiagTailX0RatChunk001Sub001Block041Part012

theorem surrogateDiagonalTailChunk001Sub001Block041Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part012] using hcert

def TailChunk001Sub001Block041Part013SupportExplicit : Finset ℕ :=
  ([26434] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part013 : ℚ :=
  (2729517015625 : ℚ) / 19070715506034081792

def SurrogateDiagonalTailChunk001Sub001Block041Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26434
    = surrogateDiagTailX0RatChunk001Sub001Block041Part013

theorem surrogateDiagonalTailChunk001Sub001Block041Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part013] using hcert

def TailChunk001Sub001Block041Part014SupportExplicit : Finset ℕ :=
  ([26435] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part014 : ℚ :=
  (248908929463 : ℚ) / 3874302529948876800

def SurrogateDiagonalTailChunk001Sub001Block041Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26435
    = surrogateDiagTailX0RatChunk001Sub001Block041Part014

theorem surrogateDiagonalTailChunk001Sub001Block041Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part014] using hcert

def TailChunk001Sub001Block041Part015SupportExplicit : Finset ℕ :=
  ([26437] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part015 : ℚ :=
  (10920546390625 : ℚ) / 305316194294598949152

def SurrogateDiagonalTailChunk001Sub001Block041Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26437
    = surrogateDiagTailX0RatChunk001Sub001Block041Part015

theorem surrogateDiagonalTailChunk001Sub001Block041Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part015] using hcert

def TailChunk001Sub001Block041Part016SupportExplicit : Finset ℕ :=
  ([26438] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part016 : ℚ :=
  (2730343140625 : ℚ) / 19082262143412434322

def SurrogateDiagonalTailChunk001Sub001Block041Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26438
    = surrogateDiagTailX0RatChunk001Sub001Block041Part016

theorem surrogateDiagonalTailChunk001Sub001Block041Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part016] using hcert

def TailChunk001Sub001Block041Part017SupportExplicit : Finset ℕ :=
  ([26439] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part017 : ℚ :=
  (179530828475 : ℚ) / 1603206218149644288

def SurrogateDiagonalTailChunk001Sub001Block041Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26439
    = surrogateDiagTailX0RatChunk001Sub001Block041Part017

theorem surrogateDiagonalTailChunk001Sub001Block041Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part017] using hcert

def TailChunk001Sub001Block041Part018SupportExplicit : Finset ℕ :=
  ([26441] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part018 : ℚ :=
  (42717151098925 : ℚ) / 1162485132371026771968

def SurrogateDiagonalTailChunk001Sub001Block041Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26441
    = surrogateDiagTailX0RatChunk001Sub001Block041Part018

theorem surrogateDiagonalTailChunk001Sub001Block041Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part018] using hcert

def TailChunk001Sub001Block041Part019SupportExplicit : Finset ℕ :=
  ([26443] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part019 : ℚ :=
  (328566168473 : ℚ) / 8538080473538979840

def SurrogateDiagonalTailChunk001Sub001Block041Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26443
    = surrogateDiagTailX0RatChunk001Sub001Block041Part019

theorem surrogateDiagonalTailChunk001Sub001Block041Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part019] using hcert

def TailChunk001Sub001Block041Part020SupportExplicit : Finset ℕ :=
  ([26445] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part020 : ℚ :=
  (47296019089 : ℚ) / 326350231484497920

def SurrogateDiagonalTailChunk001Sub001Block041Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26445
    = surrogateDiagTailX0RatChunk001Sub001Block041Part020

theorem surrogateDiagonalTailChunk001Sub001Block041Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part020] using hcert

def TailChunk001Sub001Block041Part021SupportExplicit : Finset ℕ :=
  ([26446] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part021 : ℚ :=
  (2117160841075 : ℚ) / 10293897249404485632

def SurrogateDiagonalTailChunk001Sub001Block041Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26446
    = surrogateDiagTailX0RatChunk001Sub001Block041Part021

theorem surrogateDiagonalTailChunk001Sub001Block041Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part021] using hcert

def TailChunk001Sub001Block041Part022SupportExplicit : Finset ℕ :=
  ([26447] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part022 : ℚ :=
  (7011841195825 : ℚ) / 187415866022706367488

def SurrogateDiagonalTailChunk001Sub001Block041Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26447
    = surrogateDiagTailX0RatChunk001Sub001Block041Part022

theorem surrogateDiagonalTailChunk001Sub001Block041Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part022] using hcert

def TailChunk001Sub001Block041Part023SupportExplicit : Finset ℕ :=
  ([26449] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part023 : ℚ :=
  (10930462515625 : ℚ) / 305870936271653117952

def SurrogateDiagonalTailChunk001Sub001Block041Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26449
    = surrogateDiagTailX0RatChunk001Sub001Block041Part023

theorem surrogateDiagonalTailChunk001Sub001Block041Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part023] using hcert

def TailChunk001Sub001Block041Part024SupportExplicit : Finset ℕ :=
  ([26453] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block041Part024 : ℚ :=
  (3568528495625 : ℚ) / 73356257329878575232

def SurrogateDiagonalTailChunk001Sub001Block041Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26453
    = surrogateDiagTailX0RatChunk001Sub001Block041Part024

theorem surrogateDiagonalTailChunk001Sub001Block041Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block041Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block041Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block041Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block041Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block041Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block041HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block041Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block041Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block041Part000
    + surrogateDiagTailX0RatChunk001Sub001Block041Part001
    + surrogateDiagTailX0RatChunk001Sub001Block041Part002
    + surrogateDiagTailX0RatChunk001Sub001Block041Part003
    + surrogateDiagTailX0RatChunk001Sub001Block041Part004
    + surrogateDiagTailX0RatChunk001Sub001Block041Part005
    + surrogateDiagTailX0RatChunk001Sub001Block041Part006
    + surrogateDiagTailX0RatChunk001Sub001Block041Part007
    + surrogateDiagTailX0RatChunk001Sub001Block041Part008
    + surrogateDiagTailX0RatChunk001Sub001Block041Part009

def surrogateDiagonalTailChunk001Sub001Block041MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block041Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block041Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block041Part010
    + surrogateDiagTailX0RatChunk001Sub001Block041Part011
    + surrogateDiagTailX0RatChunk001Sub001Block041Part012
    + surrogateDiagTailX0RatChunk001Sub001Block041Part013
    + surrogateDiagTailX0RatChunk001Sub001Block041Part014
    + surrogateDiagTailX0RatChunk001Sub001Block041Part015
    + surrogateDiagTailX0RatChunk001Sub001Block041Part016
    + surrogateDiagTailX0RatChunk001Sub001Block041Part017
    + surrogateDiagTailX0RatChunk001Sub001Block041Part018
    + surrogateDiagTailX0RatChunk001Sub001Block041Part019

def surrogateDiagonalTailChunk001Sub001Block041TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block041Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block041Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block041Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block041Part020
    + surrogateDiagTailX0RatChunk001Sub001Block041Part021
    + surrogateDiagTailX0RatChunk001Sub001Block041Part022
    + surrogateDiagTailX0RatChunk001Sub001Block041Part023
    + surrogateDiagTailX0RatChunk001Sub001Block041Part024

def surrogateDiagonalTailChunk001Sub001Block041Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block041HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block041MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block041TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block041 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block041Part000
    + surrogateDiagTailX0RatChunk001Sub001Block041Part001
    + surrogateDiagTailX0RatChunk001Sub001Block041Part002
    + surrogateDiagTailX0RatChunk001Sub001Block041Part003
    + surrogateDiagTailX0RatChunk001Sub001Block041Part004
    + surrogateDiagTailX0RatChunk001Sub001Block041Part005
    + surrogateDiagTailX0RatChunk001Sub001Block041Part006
    + surrogateDiagTailX0RatChunk001Sub001Block041Part007
    + surrogateDiagTailX0RatChunk001Sub001Block041Part008
    + surrogateDiagTailX0RatChunk001Sub001Block041Part009
    + surrogateDiagTailX0RatChunk001Sub001Block041Part010
    + surrogateDiagTailX0RatChunk001Sub001Block041Part011
    + surrogateDiagTailX0RatChunk001Sub001Block041Part012
    + surrogateDiagTailX0RatChunk001Sub001Block041Part013
    + surrogateDiagTailX0RatChunk001Sub001Block041Part014
    + surrogateDiagTailX0RatChunk001Sub001Block041Part015
    + surrogateDiagTailX0RatChunk001Sub001Block041Part016
    + surrogateDiagTailX0RatChunk001Sub001Block041Part017
    + surrogateDiagTailX0RatChunk001Sub001Block041Part018
    + surrogateDiagTailX0RatChunk001Sub001Block041Part019
    + surrogateDiagTailX0RatChunk001Sub001Block041Part020
    + surrogateDiagTailX0RatChunk001Sub001Block041Part021
    + surrogateDiagTailX0RatChunk001Sub001Block041Part022
    + surrogateDiagTailX0RatChunk001Sub001Block041Part023
    + surrogateDiagTailX0RatChunk001Sub001Block041Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block041_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block041Head + surrogateDiagTailX0RatChunk001Sub001Block041Mid + surrogateDiagTailX0RatChunk001Sub001Block041Tail =
      surrogateDiagTailX0RatChunk001Sub001Block041 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block041Head surrogateDiagTailX0RatChunk001Sub001Block041Mid surrogateDiagTailX0RatChunk001Sub001Block041Tail surrogateDiagTailX0RatChunk001Sub001Block041
  ring

def SurrogateDiagonalTailChunk001Sub001Block041HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block041HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block041Head

def SurrogateDiagonalTailChunk001Sub001Block041MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block041MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block041Mid

def SurrogateDiagonalTailChunk001Sub001Block041TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block041TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block041Tail

theorem surrogateDiagonalTailChunk001Sub001Block041_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block041HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block041MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block041TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block041Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block041 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block041HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block041MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block041TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block041Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block041_eq_head_add_mid_add_tail

/-- Block 042 covers tail-support indices [16050,16075) and q from 26454 to 26491. -/

def TailChunk001Sub001Block042Part000SupportExplicit : Finset ℕ :=
  ([26454] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part000 : ℚ :=
  (4858240559125 : ℚ) / 15104737593661882368

def SurrogateDiagonalTailChunk001Sub001Block042Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26454
    = surrogateDiagTailX0RatChunk001Sub001Block042Part000

theorem surrogateDiagonalTailChunk001Sub001Block042Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part000] using hcert

def TailChunk001Sub001Block042Part001SupportExplicit : Finset ℕ :=
  ([26455] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part001 : ℚ :=
  (15556626911 : ℚ) / 178357673366913024

def SurrogateDiagonalTailChunk001Sub001Block042Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26455
    = surrogateDiagTailX0RatChunk001Sub001Block042Part001

theorem surrogateDiagonalTailChunk001Sub001Block042Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part001] using hcert

def TailChunk001Sub001Block042Part002SupportExplicit : Finset ℕ :=
  ([26457] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part002 : ℚ :=
  (19439905118125 : ℚ) / 241895182672717051008

def SurrogateDiagonalTailChunk001Sub001Block042Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26457
    = surrogateDiagTailX0RatChunk001Sub001Block042Part002

theorem surrogateDiagonalTailChunk001Sub001Block042Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part002] using hcert

def TailChunk001Sub001Block042Part003SupportExplicit : Finset ℕ :=
  ([26458] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part003 : ℚ :=
  (2734475640625 : ℚ) / 19140073999750240032

def SurrogateDiagonalTailChunk001Sub001Block042Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26458
    = surrogateDiagTailX0RatChunk001Sub001Block042Part003

theorem surrogateDiagonalTailChunk001Sub001Block042Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part003] using hcert

def TailChunk001Sub001Block042Part004SupportExplicit : Finset ℕ :=
  ([26459] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part004 : ℚ :=
  (10938729390625 : ℚ) / 306333798423647782962

def SurrogateDiagonalTailChunk001Sub001Block042Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26459
    = surrogateDiagTailX0RatChunk001Sub001Block042Part004

theorem surrogateDiagonalTailChunk001Sub001Block042Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part004] using hcert

def TailChunk001Sub001Block042Part005SupportExplicit : Finset ℕ :=
  ([26461] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part005 : ℚ :=
  (10481272560325 : ℚ) / 279218028662630437152

def SurrogateDiagonalTailChunk001Sub001Block042Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26461
    = surrogateDiagTailX0RatChunk001Sub001Block042Part005

theorem surrogateDiagonalTailChunk001Sub001Block042Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part005] using hcert

def TailChunk001Sub001Block042Part006SupportExplicit : Finset ℕ :=
  ([26462] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part006 : ℚ :=
  (425351942299 : ℚ) / 2856671220000000000

def SurrogateDiagonalTailChunk001Sub001Block042Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26462
    = surrogateDiagTailX0RatChunk001Sub001Block042Part006

theorem surrogateDiagonalTailChunk001Sub001Block042Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part006] using hcert

def TailChunk001Sub001Block042Part007SupportExplicit : Finset ℕ :=
  ([26463] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part007 : ℚ :=
  (777948964717 : ℚ) / 9684588526815283200

def SurrogateDiagonalTailChunk001Sub001Block042Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26463
    = surrogateDiagTailX0RatChunk001Sub001Block042Part007

theorem surrogateDiagonalTailChunk001Sub001Block042Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part007] using hcert

def TailChunk001Sub001Block042Part008SupportExplicit : Finset ℕ :=
  ([26465] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part008 : ℚ :=
  (8890757721025 : ℚ) / 149864828972446089216

def SurrogateDiagonalTailChunk001Sub001Block042Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26465
    = surrogateDiagTailX0RatChunk001Sub001Block042Part008

theorem surrogateDiagonalTailChunk001Sub001Block042Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part008] using hcert

def TailChunk001Sub001Block042Part009SupportExplicit : Finset ℕ :=
  ([26466] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part009 : ℚ :=
  (168640724413 : ℚ) / 409681920000000000

def SurrogateDiagonalTailChunk001Sub001Block042Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26466
    = surrogateDiagTailX0RatChunk001Sub001Block042Part009

theorem surrogateDiagonalTailChunk001Sub001Block042Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part009] using hcert

def TailChunk001Sub001Block042Part010SupportExplicit : Finset ℕ :=
  ([26467] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part010 : ℚ :=
  (7232008499875 : ℚ) / 130714164267837460992

def SurrogateDiagonalTailChunk001Sub001Block042Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26467
    = surrogateDiagTailX0RatChunk001Sub001Block042Part010

theorem surrogateDiagonalTailChunk001Sub001Block042Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part010] using hcert

def TailChunk001Sub001Block042Part011SupportExplicit : Finset ℕ :=
  ([26470] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part011 : ℚ :=
  (7440848767525 : ℚ) / 31378066826881517568

def SurrogateDiagonalTailChunk001Sub001Block042Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26470
    = surrogateDiagTailX0RatChunk001Sub001Block042Part011

theorem surrogateDiagonalTailChunk001Sub001Block042Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part011] using hcert

def TailChunk001Sub001Block042Part012SupportExplicit : Finset ℕ :=
  ([26471] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part012 : ℚ :=
  (4746896637625 : ℚ) / 129165014707891863552

def SurrogateDiagonalTailChunk001Sub001Block042Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26471
    = surrogateDiagTailX0RatChunk001Sub001Block042Part012

theorem surrogateDiagonalTailChunk001Sub001Block042Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part012] using hcert

def TailChunk001Sub001Block042Part013SupportExplicit : Finset ℕ :=
  ([26473] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part013 : ℚ :=
  (33552079179 : ℚ) / 853744064878375000

def SurrogateDiagonalTailChunk001Sub001Block042Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26473
    = surrogateDiagTailX0RatChunk001Sub001Block042Part013

theorem surrogateDiagonalTailChunk001Sub001Block042Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part013] using hcert

def TailChunk001Sub001Block042Part014SupportExplicit : Finset ℕ :=
  ([26474] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part014 : ℚ :=
  (15708528011 : ℚ) / 68038052889600000

def SurrogateDiagonalTailChunk001Sub001Block042Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26474
    = surrogateDiagTailX0RatChunk001Sub001Block042Part014

theorem surrogateDiagonalTailChunk001Sub001Block042Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part014] using hcert

def TailChunk001Sub001Block042Part015SupportExplicit : Finset ℕ :=
  ([26477] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part015 : ℚ :=
  (671894623259 : ℚ) / 13897746619253145600

def SurrogateDiagonalTailChunk001Sub001Block042Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26477
    = surrogateDiagTailX0RatChunk001Sub001Block042Part015

theorem surrogateDiagonalTailChunk001Sub001Block042Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part015] using hcert

def TailChunk001Sub001Block042Part016SupportExplicit : Finset ℕ :=
  ([26479] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part016 : ℚ :=
  (10955272515625 : ℚ) / 307261098497679603282

def SurrogateDiagonalTailChunk001Sub001Block042Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26479
    = surrogateDiagTailX0RatChunk001Sub001Block042Part016

theorem surrogateDiagonalTailChunk001Sub001Block042Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part016] using hcert

def TailChunk001Sub001Block042Part017SupportExplicit : Finset ℕ :=
  ([26481] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part017 : ℚ :=
  (1385619833825 : ℚ) / 10146569862651052032

def SurrogateDiagonalTailChunk001Sub001Block042Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26481
    = surrogateDiagTailX0RatChunk001Sub001Block042Part017

theorem surrogateDiagonalTailChunk001Sub001Block042Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part017] using hcert

def TailChunk001Sub001Block042Part018SupportExplicit : Finset ℕ :=
  ([26482] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part018 : ℚ :=
  (4383102025 : ℚ) / 30735394415473152

def SurrogateDiagonalTailChunk001Sub001Block042Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26482
    = surrogateDiagTailX0RatChunk001Sub001Block042Part018

theorem surrogateDiagonalTailChunk001Sub001Block042Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part018] using hcert

def TailChunk001Sub001Block042Part019SupportExplicit : Finset ℕ :=
  ([26483] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part019 : ℚ :=
  (1700318424001 : ℚ) / 45988661518981171200

def SurrogateDiagonalTailChunk001Sub001Block042Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26483
    = surrogateDiagTailX0RatChunk001Sub001Block042Part019

theorem surrogateDiagonalTailChunk001Sub001Block042Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part019] using hcert

def TailChunk001Sub001Block042Part020SupportExplicit : Finset ℕ :=
  ([26485] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part020 : ℚ :=
  (1753054140625 : ℚ) / 31473043881444507648

def SurrogateDiagonalTailChunk001Sub001Block042Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26485
    = surrogateDiagTailX0RatChunk001Sub001Block042Part020

theorem surrogateDiagonalTailChunk001Sub001Block042Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part020] using hcert

def TailChunk001Sub001Block042Part021SupportExplicit : Finset ℕ :=
  ([26486] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part021 : ℚ :=
  (349662545953 : ℚ) / 1761557267821363200

def SurrogateDiagonalTailChunk001Sub001Block042Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26486
    = surrogateDiagTailX0RatChunk001Sub001Block042Part021

theorem surrogateDiagonalTailChunk001Sub001Block042Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part021] using hcert

def TailChunk001Sub001Block042Part022SupportExplicit : Finset ℕ :=
  ([26489] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part022 : ℚ :=
  (10963548765625 : ℚ) / 307725537213915566592

def SurrogateDiagonalTailChunk001Sub001Block042Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26489
    = surrogateDiagTailX0RatChunk001Sub001Block042Part022

theorem surrogateDiagonalTailChunk001Sub001Block042Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part022] using hcert

def TailChunk001Sub001Block042Part023SupportExplicit : Finset ℕ :=
  ([26490] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part023 : ℚ :=
  (3454432921075 : ℚ) / 6198136657161781248

def SurrogateDiagonalTailChunk001Sub001Block042Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26490
    = surrogateDiagTailX0RatChunk001Sub001Block042Part023

theorem surrogateDiagonalTailChunk001Sub001Block042Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part023] using hcert

def TailChunk001Sub001Block042Part024SupportExplicit : Finset ℕ :=
  ([26491] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block042Part024 : ℚ :=
  (42344093341675 : ℚ) / 1139858360862158880768

def SurrogateDiagonalTailChunk001Sub001Block042Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26491
    = surrogateDiagTailX0RatChunk001Sub001Block042Part024

theorem surrogateDiagonalTailChunk001Sub001Block042Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block042Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block042Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block042Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block042Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block042Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block042HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block042Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block042Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block042Part000
    + surrogateDiagTailX0RatChunk001Sub001Block042Part001
    + surrogateDiagTailX0RatChunk001Sub001Block042Part002
    + surrogateDiagTailX0RatChunk001Sub001Block042Part003
    + surrogateDiagTailX0RatChunk001Sub001Block042Part004
    + surrogateDiagTailX0RatChunk001Sub001Block042Part005
    + surrogateDiagTailX0RatChunk001Sub001Block042Part006
    + surrogateDiagTailX0RatChunk001Sub001Block042Part007
    + surrogateDiagTailX0RatChunk001Sub001Block042Part008
    + surrogateDiagTailX0RatChunk001Sub001Block042Part009

def surrogateDiagonalTailChunk001Sub001Block042MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block042Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block042Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block042Part010
    + surrogateDiagTailX0RatChunk001Sub001Block042Part011
    + surrogateDiagTailX0RatChunk001Sub001Block042Part012
    + surrogateDiagTailX0RatChunk001Sub001Block042Part013
    + surrogateDiagTailX0RatChunk001Sub001Block042Part014
    + surrogateDiagTailX0RatChunk001Sub001Block042Part015
    + surrogateDiagTailX0RatChunk001Sub001Block042Part016
    + surrogateDiagTailX0RatChunk001Sub001Block042Part017
    + surrogateDiagTailX0RatChunk001Sub001Block042Part018
    + surrogateDiagTailX0RatChunk001Sub001Block042Part019

def surrogateDiagonalTailChunk001Sub001Block042TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block042Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block042Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block042Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block042Part020
    + surrogateDiagTailX0RatChunk001Sub001Block042Part021
    + surrogateDiagTailX0RatChunk001Sub001Block042Part022
    + surrogateDiagTailX0RatChunk001Sub001Block042Part023
    + surrogateDiagTailX0RatChunk001Sub001Block042Part024

def surrogateDiagonalTailChunk001Sub001Block042Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block042HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block042MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block042TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block042 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block042Part000
    + surrogateDiagTailX0RatChunk001Sub001Block042Part001
    + surrogateDiagTailX0RatChunk001Sub001Block042Part002
    + surrogateDiagTailX0RatChunk001Sub001Block042Part003
    + surrogateDiagTailX0RatChunk001Sub001Block042Part004
    + surrogateDiagTailX0RatChunk001Sub001Block042Part005
    + surrogateDiagTailX0RatChunk001Sub001Block042Part006
    + surrogateDiagTailX0RatChunk001Sub001Block042Part007
    + surrogateDiagTailX0RatChunk001Sub001Block042Part008
    + surrogateDiagTailX0RatChunk001Sub001Block042Part009
    + surrogateDiagTailX0RatChunk001Sub001Block042Part010
    + surrogateDiagTailX0RatChunk001Sub001Block042Part011
    + surrogateDiagTailX0RatChunk001Sub001Block042Part012
    + surrogateDiagTailX0RatChunk001Sub001Block042Part013
    + surrogateDiagTailX0RatChunk001Sub001Block042Part014
    + surrogateDiagTailX0RatChunk001Sub001Block042Part015
    + surrogateDiagTailX0RatChunk001Sub001Block042Part016
    + surrogateDiagTailX0RatChunk001Sub001Block042Part017
    + surrogateDiagTailX0RatChunk001Sub001Block042Part018
    + surrogateDiagTailX0RatChunk001Sub001Block042Part019
    + surrogateDiagTailX0RatChunk001Sub001Block042Part020
    + surrogateDiagTailX0RatChunk001Sub001Block042Part021
    + surrogateDiagTailX0RatChunk001Sub001Block042Part022
    + surrogateDiagTailX0RatChunk001Sub001Block042Part023
    + surrogateDiagTailX0RatChunk001Sub001Block042Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block042_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block042Head + surrogateDiagTailX0RatChunk001Sub001Block042Mid + surrogateDiagTailX0RatChunk001Sub001Block042Tail =
      surrogateDiagTailX0RatChunk001Sub001Block042 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block042Head surrogateDiagTailX0RatChunk001Sub001Block042Mid surrogateDiagTailX0RatChunk001Sub001Block042Tail surrogateDiagTailX0RatChunk001Sub001Block042
  ring

def SurrogateDiagonalTailChunk001Sub001Block042HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block042HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block042Head

def SurrogateDiagonalTailChunk001Sub001Block042MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block042MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block042Mid

def SurrogateDiagonalTailChunk001Sub001Block042TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block042TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block042Tail

theorem surrogateDiagonalTailChunk001Sub001Block042_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block042HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block042MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block042TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block042Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block042 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block042HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block042MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block042TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block042Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block042_eq_head_add_mid_add_tail

/-- Block 043 covers tail-support indices [16075,16100) and q from 26493 to 26534. -/

def TailChunk001Sub001Block043Part000SupportExplicit : Finset ℕ :=
  ([26493] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part000 : ℚ :=
  (779713964677 : ℚ) / 9728584315333507200

def SurrogateDiagonalTailChunk001Sub001Block043Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26493
    = surrogateDiagTailX0RatChunk001Sub001Block043Part000

theorem surrogateDiagonalTailChunk001Sub001Block043Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part000] using hcert

def TailChunk001Sub001Block043Part001SupportExplicit : Finset ℕ :=
  ([26494] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part001 : ℚ :=
  (1598471554075 : ℚ) / 9280934436636822528

def SurrogateDiagonalTailChunk001Sub001Block043Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26494
    = surrogateDiagTailX0RatChunk001Sub001Block043Part001

theorem surrogateDiagonalTailChunk001Sub001Block043Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part001] using hcert

def TailChunk001Sub001Block043Part002SupportExplicit : Finset ℕ :=
  ([26495] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part002 : ℚ :=
  (2310533889725 : ℚ) / 30110398154575183872

def SurrogateDiagonalTailChunk001Sub001Block043Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26495
    = surrogateDiagTailX0RatChunk001Sub001Block043Part002

theorem surrogateDiagonalTailChunk001Sub001Block043Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part002] using hcert

def TailChunk001Sub001Block043Part003SupportExplicit : Finset ℕ :=
  ([26497] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part003 : ℚ :=
  (10970172015625 : ℚ) / 308097467115248812032

def SurrogateDiagonalTailChunk001Sub001Block043Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26497
    = surrogateDiagTailX0RatChunk001Sub001Block043Part003

theorem surrogateDiagonalTailChunk001Sub001Block043Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part003] using hcert

def TailChunk001Sub001Block043Part004SupportExplicit : Finset ℕ :=
  ([26498] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part004 : ℚ :=
  (2742750015625 : ℚ) / 19256091694703050752

def SurrogateDiagonalTailChunk001Sub001Block043Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26498
    = surrogateDiagTailX0RatChunk001Sub001Block043Part004

theorem surrogateDiagonalTailChunk001Sub001Block043Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part004] using hcert

def TailChunk001Sub001Block043Part005SupportExplicit : Finset ℕ :=
  ([26501] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part005 : ℚ :=
  (702303001 : ℚ) / 19730147740500000

def SurrogateDiagonalTailChunk001Sub001Block043Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26501
    = surrogateDiagTailX0RatChunk001Sub001Block043Part005

theorem surrogateDiagonalTailChunk001Sub001Block043Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part005] using hcert

def TailChunk001Sub001Block043Part006SupportExplicit : Finset ℕ :=
  ([26502] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part006 : ℚ :=
  (10923978329 : ℚ) / 23337052141132800

def SurrogateDiagonalTailChunk001Sub001Block043Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26502
    = surrogateDiagTailX0RatChunk001Sub001Block043Part006

theorem surrogateDiagonalTailChunk001Sub001Block043Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part006] using hcert

def TailChunk001Sub001Block043Part007SupportExplicit : Finset ℕ :=
  ([26503] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part007 : ℚ :=
  (9787024873075 : ℚ) / 241388519739133919232

def SurrogateDiagonalTailChunk001Sub001Block043Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26503
    = surrogateDiagTailX0RatChunk001Sub001Block043Part007

theorem surrogateDiagonalTailChunk001Sub001Block043Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part007] using hcert

def TailChunk001Sub001Block043Part008SupportExplicit : Finset ℕ :=
  ([26506] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part008 : ℚ :=
  (10328721174325 : ℚ) / 66453575808267583488

def SurrogateDiagonalTailChunk001Sub001Block043Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26506
    = surrogateDiagTailX0RatChunk001Sub001Block043Part008

theorem surrogateDiagonalTailChunk001Sub001Block043Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part008] using hcert

def TailChunk001Sub001Block043Part009SupportExplicit : Finset ℕ :=
  ([26507] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part009 : ℚ :=
  (12548524515275 : ℚ) / 298158577007873366016

def SurrogateDiagonalTailChunk001Sub001Block043Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26507
    = surrogateDiagTailX0RatChunk001Sub001Block043Part009

theorem surrogateDiagonalTailChunk001Sub001Block043Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part009] using hcert

def TailChunk001Sub001Block043Part010SupportExplicit : Finset ℕ :=
  ([26510] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part010 : ℚ :=
  (7130525719 : ℚ) / 23597678592000000

def SurrogateDiagonalTailChunk001Sub001Block043Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26510
    = surrogateDiagTailX0RatChunk001Sub001Block043Part010

theorem surrogateDiagonalTailChunk001Sub001Block043Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part010] using hcert

def TailChunk001Sub001Block043Part011SupportExplicit : Finset ℕ :=
  ([26511] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part011 : ℚ :=
  (19519348116325 : ℚ) / 243876340931515926528

def SurrogateDiagonalTailChunk001Sub001Block043Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26511
    = surrogateDiagTailX0RatChunk001Sub001Block043Part011

theorem surrogateDiagonalTailChunk001Sub001Block043Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part011] using hcert

def TailChunk001Sub001Block043Part012SupportExplicit : Finset ℕ :=
  ([26513] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part012 : ℚ :=
  (10983424515625 : ℚ) / 308842338258421358592

def SurrogateDiagonalTailChunk001Sub001Block043Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26513
    = surrogateDiagTailX0RatChunk001Sub001Block043Part012

theorem surrogateDiagonalTailChunk001Sub001Block043Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part012] using hcert

def TailChunk001Sub001Block043Part013SupportExplicit : Finset ℕ :=
  ([26515] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part013 : ℚ :=
  (1757028390625 : ℚ) / 31615913531507276928

def SurrogateDiagonalTailChunk001Sub001Block043Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26515
    = surrogateDiagTailX0RatChunk001Sub001Block043Part013

theorem surrogateDiagonalTailChunk001Sub001Block043Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part013] using hcert

def TailChunk001Sub001Block043Part014SupportExplicit : Finset ℕ :=
  ([26517] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part014 : ℚ :=
  (19528185116125 : ℚ) / 244097218391323356288

def SurrogateDiagonalTailChunk001Sub001Block043Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26517
    = surrogateDiagTailX0RatChunk001Sub001Block043Part014

theorem surrogateDiagonalTailChunk001Sub001Block043Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part014] using hcert

def TailChunk001Sub001Block043Part015SupportExplicit : Finset ℕ :=
  ([26518] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part015 : ℚ :=
  (2746891890625 : ℚ) / 19314297930537483762

def SurrogateDiagonalTailChunk001Sub001Block043Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26518
    = surrogateDiagTailX0RatChunk001Sub001Block043Part015

theorem surrogateDiagonalTailChunk001Sub001Block043Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part015] using hcert

def TailChunk001Sub001Block043Part016SupportExplicit : Finset ℕ :=
  ([26519] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part016 : ℚ :=
  (20201318244275 : ℚ) / 515819199163451572224

def SurrogateDiagonalTailChunk001Sub001Block043Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26519
    = surrogateDiagTailX0RatChunk001Sub001Block043Part016

theorem surrogateDiagonalTailChunk001Sub001Block043Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part016] using hcert

def TailChunk001Sub001Block043Part017SupportExplicit : Finset ℕ :=
  ([26521] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part017 : ℚ :=
  (146672811001 : ℚ) / 3374077241512200000

def SurrogateDiagonalTailChunk001Sub001Block043Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26521
    = surrogateDiagTailX0RatChunk001Sub001Block043Part017

theorem surrogateDiagonalTailChunk001Sub001Block043Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part017] using hcert

def TailChunk001Sub001Block043Part018SupportExplicit : Finset ℕ :=
  ([26522] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part018 : ℚ :=
  (10675433973175 : ℚ) / 71945628206341029888

def SurrogateDiagonalTailChunk001Sub001Block043Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26522
    = surrogateDiagTailX0RatChunk001Sub001Block043Part018

theorem surrogateDiagonalTailChunk001Sub001Block043Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part018] using hcert

def TailChunk001Sub001Block043Part019SupportExplicit : Finset ℕ :=
  ([26526] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part019 : ℚ :=
  (195388982317 : ℚ) / 610795614631987200

def SurrogateDiagonalTailChunk001Sub001Block043Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26526
    = surrogateDiagTailX0RatChunk001Sub001Block043Part019

theorem surrogateDiagonalTailChunk001Sub001Block043Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part019] using hcert

def TailChunk001Sub001Block043Part020SupportExplicit : Finset ℕ :=
  ([26527] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part020 : ℚ :=
  (52411584731 : ℚ) / 1393499795078169600

def SurrogateDiagonalTailChunk001Sub001Block043Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26527
    = surrogateDiagTailX0RatChunk001Sub001Block043Part020

theorem surrogateDiagonalTailChunk001Sub001Block043Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part020] using hcert

def TailChunk001Sub001Block043Part021SupportExplicit : Finset ℕ :=
  ([26529] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part021 : ℚ :=
  (18505693374325 : ℚ) / 215607901600503595008

def SurrogateDiagonalTailChunk001Sub001Block043Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26529
    = surrogateDiagTailX0RatChunk001Sub001Block043Part021

theorem surrogateDiagonalTailChunk001Sub001Block043Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part021] using hcert

def TailChunk001Sub001Block043Part022SupportExplicit : Finset ℕ :=
  ([26530] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part022 : ℚ :=
  (2919718821725 : ℚ) / 8468549480974270464

def SurrogateDiagonalTailChunk001Sub001Block043Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26530
    = surrogateDiagTailX0RatChunk001Sub001Block043Part022

theorem surrogateDiagonalTailChunk001Sub001Block043Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part022] using hcert

def TailChunk001Sub001Block043Part023SupportExplicit : Finset ℕ :=
  ([26531] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part023 : ℚ :=
  (21008359761575 : ℚ) / 560166165416701476864

def SurrogateDiagonalTailChunk001Sub001Block043Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26531
    = surrogateDiagTailX0RatChunk001Sub001Block043Part023

theorem surrogateDiagonalTailChunk001Sub001Block043Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part023] using hcert

def TailChunk001Sub001Block043Part024SupportExplicit : Finset ℕ :=
  ([26534] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block043Part024 : ℚ :=
  (2750207640625 : ℚ) / 19360957846913135442

def SurrogateDiagonalTailChunk001Sub001Block043Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26534
    = surrogateDiagTailX0RatChunk001Sub001Block043Part024

theorem surrogateDiagonalTailChunk001Sub001Block043Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block043Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block043Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block043Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block043Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block043Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block043HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block043Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block043Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block043Part000
    + surrogateDiagTailX0RatChunk001Sub001Block043Part001
    + surrogateDiagTailX0RatChunk001Sub001Block043Part002
    + surrogateDiagTailX0RatChunk001Sub001Block043Part003
    + surrogateDiagTailX0RatChunk001Sub001Block043Part004
    + surrogateDiagTailX0RatChunk001Sub001Block043Part005
    + surrogateDiagTailX0RatChunk001Sub001Block043Part006
    + surrogateDiagTailX0RatChunk001Sub001Block043Part007
    + surrogateDiagTailX0RatChunk001Sub001Block043Part008
    + surrogateDiagTailX0RatChunk001Sub001Block043Part009

def surrogateDiagonalTailChunk001Sub001Block043MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block043Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block043Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block043Part010
    + surrogateDiagTailX0RatChunk001Sub001Block043Part011
    + surrogateDiagTailX0RatChunk001Sub001Block043Part012
    + surrogateDiagTailX0RatChunk001Sub001Block043Part013
    + surrogateDiagTailX0RatChunk001Sub001Block043Part014
    + surrogateDiagTailX0RatChunk001Sub001Block043Part015
    + surrogateDiagTailX0RatChunk001Sub001Block043Part016
    + surrogateDiagTailX0RatChunk001Sub001Block043Part017
    + surrogateDiagTailX0RatChunk001Sub001Block043Part018
    + surrogateDiagTailX0RatChunk001Sub001Block043Part019

def surrogateDiagonalTailChunk001Sub001Block043TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block043Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block043Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block043Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block043Part020
    + surrogateDiagTailX0RatChunk001Sub001Block043Part021
    + surrogateDiagTailX0RatChunk001Sub001Block043Part022
    + surrogateDiagTailX0RatChunk001Sub001Block043Part023
    + surrogateDiagTailX0RatChunk001Sub001Block043Part024

def surrogateDiagonalTailChunk001Sub001Block043Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block043HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block043MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block043TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block043 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block043Part000
    + surrogateDiagTailX0RatChunk001Sub001Block043Part001
    + surrogateDiagTailX0RatChunk001Sub001Block043Part002
    + surrogateDiagTailX0RatChunk001Sub001Block043Part003
    + surrogateDiagTailX0RatChunk001Sub001Block043Part004
    + surrogateDiagTailX0RatChunk001Sub001Block043Part005
    + surrogateDiagTailX0RatChunk001Sub001Block043Part006
    + surrogateDiagTailX0RatChunk001Sub001Block043Part007
    + surrogateDiagTailX0RatChunk001Sub001Block043Part008
    + surrogateDiagTailX0RatChunk001Sub001Block043Part009
    + surrogateDiagTailX0RatChunk001Sub001Block043Part010
    + surrogateDiagTailX0RatChunk001Sub001Block043Part011
    + surrogateDiagTailX0RatChunk001Sub001Block043Part012
    + surrogateDiagTailX0RatChunk001Sub001Block043Part013
    + surrogateDiagTailX0RatChunk001Sub001Block043Part014
    + surrogateDiagTailX0RatChunk001Sub001Block043Part015
    + surrogateDiagTailX0RatChunk001Sub001Block043Part016
    + surrogateDiagTailX0RatChunk001Sub001Block043Part017
    + surrogateDiagTailX0RatChunk001Sub001Block043Part018
    + surrogateDiagTailX0RatChunk001Sub001Block043Part019
    + surrogateDiagTailX0RatChunk001Sub001Block043Part020
    + surrogateDiagTailX0RatChunk001Sub001Block043Part021
    + surrogateDiagTailX0RatChunk001Sub001Block043Part022
    + surrogateDiagTailX0RatChunk001Sub001Block043Part023
    + surrogateDiagTailX0RatChunk001Sub001Block043Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block043_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block043Head + surrogateDiagTailX0RatChunk001Sub001Block043Mid + surrogateDiagTailX0RatChunk001Sub001Block043Tail =
      surrogateDiagTailX0RatChunk001Sub001Block043 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block043Head surrogateDiagTailX0RatChunk001Sub001Block043Mid surrogateDiagTailX0RatChunk001Sub001Block043Tail surrogateDiagTailX0RatChunk001Sub001Block043
  ring

def SurrogateDiagonalTailChunk001Sub001Block043HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block043HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block043Head

def SurrogateDiagonalTailChunk001Sub001Block043MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block043MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block043Mid

def SurrogateDiagonalTailChunk001Sub001Block043TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block043TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block043Tail

theorem surrogateDiagonalTailChunk001Sub001Block043_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block043HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block043MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block043TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block043Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block043 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block043HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block043MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block043TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block043Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block043_eq_head_add_mid_add_tail

/-- Block 044 covers tail-support indices [16100,16125) and q from 26535 to 26574. -/

def TailChunk001Sub001Block044Part000SupportExplicit : Finset ℕ :=
  ([26535] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part000 : ℚ :=
  (47329390159 : ℚ) / 326350231484497920

def SurrogateDiagonalTailChunk001Sub001Block044Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26535
    = surrogateDiagTailX0RatChunk001Sub001Block044Part000

theorem surrogateDiagonalTailChunk001Sub001Block044Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part000] using hcert

def TailChunk001Sub001Block044Part001SupportExplicit : Finset ℕ :=
  ([26537] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part001 : ℚ :=
  (7371010400725 : ℚ) / 128962575414740385792

def SurrogateDiagonalTailChunk001Sub001Block044Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26537
    = surrogateDiagTailX0RatChunk001Sub001Block044Part001

theorem surrogateDiagonalTailChunk001Sub001Block044Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part001] using hcert

def TailChunk001Sub001Block044Part002SupportExplicit : Finset ℕ :=
  ([26538] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part002 : ℚ :=
  (444467777975 : ℚ) / 1390686085524624768

def SurrogateDiagonalTailChunk001Sub001Block044Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26538
    = surrogateDiagTailX0RatChunk001Sub001Block044Part002

theorem surrogateDiagonalTailChunk001Sub001Block044Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part002] using hcert

def TailChunk001Sub001Block044Part003SupportExplicit : Finset ℕ :=
  ([26539] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part003 : ℚ :=
  (11004976890625 : ℚ) / 310055633484774774642

def SurrogateDiagonalTailChunk001Sub001Block044Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26539
    = surrogateDiagTailX0RatChunk001Sub001Block044Part003

theorem surrogateDiagonalTailChunk001Sub001Block044Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part003] using hcert

def TailChunk001Sub001Block044Part004SupportExplicit : Finset ℕ :=
  ([26542] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part004 : ℚ :=
  (10504288675 : ℚ) / 66334773554970624

def SurrogateDiagonalTailChunk001Sub001Block044Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26542
    = surrogateDiagTailX0RatChunk001Sub001Block044Part004

theorem surrogateDiagonalTailChunk001Sub001Block044Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part004] using hcert

def TailChunk001Sub001Block044Part005SupportExplicit : Finset ℕ :=
  ([26543] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part005 : ℚ :=
  (82142901397 : ℚ) / 1654013570502787200

def SurrogateDiagonalTailChunk001Sub001Block044Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26543
    = surrogateDiagTailX0RatChunk001Sub001Block044Part005

theorem surrogateDiagonalTailChunk001Sub001Block044Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part005] using hcert

def TailChunk001Sub001Block044Part006SupportExplicit : Finset ℕ :=
  ([26545] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part006 : ℚ :=
  (1761007140625 : ℚ) / 31759269040431187968

def SurrogateDiagonalTailChunk001Sub001Block044Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26545
    = surrogateDiagTailX0RatChunk001Sub001Block044Part006

theorem surrogateDiagonalTailChunk001Sub001Block044Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part006] using hcert

def TailChunk001Sub001Block044Part007SupportExplicit : Finset ℕ :=
  ([26546] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part007 : ℚ :=
  (192570732053 : ℚ) / 1122490116620697600

def SurrogateDiagonalTailChunk001Sub001Block044Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26546
    = surrogateDiagTailX0RatChunk001Sub001Block044Part007

theorem surrogateDiagonalTailChunk001Sub001Block044Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part007] using hcert

def TailChunk001Sub001Block044Part008SupportExplicit : Finset ℕ :=
  ([26547] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part008 : ℚ :=
  (19572400115125 : ℚ) / 245203857073494294528

def SurrogateDiagonalTailChunk001Sub001Block044Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26547
    = surrogateDiagTailX0RatChunk001Sub001Block044Part008

theorem surrogateDiagonalTailChunk001Sub001Block044Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part008] using hcert

def TailChunk001Sub001Block044Part009SupportExplicit : Finset ℕ :=
  ([26549] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part009 : ℚ :=
  (172276763299 : ℚ) / 4727348281945869120

def SurrogateDiagonalTailChunk001Sub001Block044Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26549
    = surrogateDiagTailX0RatChunk001Sub001Block044Part009

theorem surrogateDiagonalTailChunk001Sub001Block044Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part009] using hcert

def TailChunk001Sub001Block044Part010SupportExplicit : Finset ℕ :=
  ([26551] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part010 : ℚ :=
  (33256073596225 : ℚ) / 670046858083796779008

def SurrogateDiagonalTailChunk001Sub001Block044Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26551
    = surrogateDiagTailX0RatChunk001Sub001Block044Part010

theorem surrogateDiagonalTailChunk001Sub001Block044Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part010] using hcert

def TailChunk001Sub001Block044Part011SupportExplicit : Finset ℕ :=
  ([26553] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part011 : ℚ :=
  (1442256423775 : ℚ) / 17086346759904854016

def SurrogateDiagonalTailChunk001Sub001Block044Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26553
    = surrogateDiagTailX0RatChunk001Sub001Block044Part011

theorem surrogateDiagonalTailChunk001Sub001Block044Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part011] using hcert

def TailChunk001Sub001Block044Part012SupportExplicit : Finset ℕ :=
  ([26554] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part012 : ℚ :=
  (331858147603 : ℚ) / 1573834063872000000

def SurrogateDiagonalTailChunk001Sub001Block044Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26554
    = surrogateDiagTailX0RatChunk001Sub001Block044Part012

theorem surrogateDiagonalTailChunk001Sub001Block044Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part012] using hcert

def TailChunk001Sub001Block044Part013SupportExplicit : Finset ℕ :=
  ([26555] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part013 : ℚ :=
  (26726132515825 : ℚ) / 450993457426436456448

def SurrogateDiagonalTailChunk001Sub001Block044Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26555
    = surrogateDiagTailX0RatChunk001Sub001Block044Part013

theorem surrogateDiagonalTailChunk001Sub001Block044Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part013] using hcert

def TailChunk001Sub001Block044Part014SupportExplicit : Finset ℕ :=
  ([26557] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part014 : ℚ :=
  (11019910140625 : ℚ) / 310897698769539201312

def SurrogateDiagonalTailChunk001Sub001Block044Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26557
    = surrogateDiagTailX0RatChunk001Sub001Block044Part014

theorem surrogateDiagonalTailChunk001Sub001Block044Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part014] using hcert

def TailChunk001Sub001Block044Part015SupportExplicit : Finset ℕ :=
  ([26561] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part015 : ℚ :=
  (17637168025 : ℚ) / 497736091321761792

def SurrogateDiagonalTailChunk001Sub001Block044Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26561
    = surrogateDiagTailX0RatChunk001Sub001Block044Part015

theorem surrogateDiagonalTailChunk001Sub001Block044Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part015] using hcert

def TailChunk001Sub001Block044Part016SupportExplicit : Finset ℕ :=
  ([26562] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part016 : ℚ :=
  (931586801825 : ℚ) / 2027858050035744768

def SurrogateDiagonalTailChunk001Sub001Block044Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26562
    = surrogateDiagTailX0RatChunk001Sub001Block044Part016

theorem surrogateDiagonalTailChunk001Sub001Block044Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part016] using hcert

def TailChunk001Sub001Block044Part017SupportExplicit : Finset ℕ :=
  ([26563] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part017 : ℚ :=
  (860269453559 : ℚ) / 23564705678736000000

def SurrogateDiagonalTailChunk001Sub001Block044Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26563
    = surrogateDiagTailX0RatChunk001Sub001Block044Part017

theorem surrogateDiagonalTailChunk001Sub001Block044Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part017] using hcert

def TailChunk001Sub001Block044Part018SupportExplicit : Finset ℕ :=
  ([26565] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part018 : ℚ :=
  (158737109819 : ℚ) / 621888502077849600

def SurrogateDiagonalTailChunk001Sub001Block044Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26565
    = surrogateDiagTailX0RatChunk001Sub001Block044Part018

theorem surrogateDiagonalTailChunk001Sub001Block044Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part018] using hcert

def TailChunk001Sub001Block044Part019SupportExplicit : Finset ℕ :=
  ([26566] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part019 : ℚ :=
  (82014221975 : ℚ) / 538963058500768656

def SurrogateDiagonalTailChunk001Sub001Block044Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26566
    = surrogateDiagTailX0RatChunk001Sub001Block044Part019

theorem surrogateDiagonalTailChunk001Sub001Block044Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part019] using hcert

def TailChunk001Sub001Block044Part020SupportExplicit : Finset ℕ :=
  ([26567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part020 : ℚ :=
  (110552613023 : ℚ) / 2899850900967751680

def SurrogateDiagonalTailChunk001Sub001Block044Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26567
    = surrogateDiagTailX0RatChunk001Sub001Block044Part020

theorem surrogateDiagonalTailChunk001Sub001Block044Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part020] using hcert

def TailChunk001Sub001Block044Part021SupportExplicit : Finset ℕ :=
  ([26570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part021 : ℚ :=
  (7497187820275 : ℚ) / 31855109844592754688

def SurrogateDiagonalTailChunk001Sub001Block044Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26570
    = surrogateDiagTailX0RatChunk001Sub001Block044Part021

theorem surrogateDiagonalTailChunk001Sub001Block044Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part021] using hcert

def TailChunk001Sub001Block044Part022SupportExplicit : Finset ℕ :=
  ([26571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part022 : ℚ :=
  (352395615029 : ℚ) / 3834159207913881600

def SurrogateDiagonalTailChunk001Sub001Block044Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26571
    = surrogateDiagTailX0RatChunk001Sub001Block044Part022

theorem surrogateDiagonalTailChunk001Sub001Block044Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part022] using hcert

def TailChunk001Sub001Block044Part023SupportExplicit : Finset ℕ :=
  ([26573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part023 : ℚ :=
  (11033192640625 : ℚ) / 311647640111585555232

def SurrogateDiagonalTailChunk001Sub001Block044Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26573
    = surrogateDiagTailX0RatChunk001Sub001Block044Part023

theorem surrogateDiagonalTailChunk001Sub001Block044Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part023] using hcert

def TailChunk001Sub001Block044Part024SupportExplicit : Finset ℕ :=
  ([26574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block044Part024 : ℚ :=
  (2910574328975 : ℚ) / 6737746925015737344

def SurrogateDiagonalTailChunk001Sub001Block044Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26574
    = surrogateDiagTailX0RatChunk001Sub001Block044Part024

theorem surrogateDiagonalTailChunk001Sub001Block044Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block044Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block044Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block044Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block044Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block044Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block044HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block044Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block044Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block044Part000
    + surrogateDiagTailX0RatChunk001Sub001Block044Part001
    + surrogateDiagTailX0RatChunk001Sub001Block044Part002
    + surrogateDiagTailX0RatChunk001Sub001Block044Part003
    + surrogateDiagTailX0RatChunk001Sub001Block044Part004
    + surrogateDiagTailX0RatChunk001Sub001Block044Part005
    + surrogateDiagTailX0RatChunk001Sub001Block044Part006
    + surrogateDiagTailX0RatChunk001Sub001Block044Part007
    + surrogateDiagTailX0RatChunk001Sub001Block044Part008
    + surrogateDiagTailX0RatChunk001Sub001Block044Part009

def surrogateDiagonalTailChunk001Sub001Block044MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block044Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block044Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block044Part010
    + surrogateDiagTailX0RatChunk001Sub001Block044Part011
    + surrogateDiagTailX0RatChunk001Sub001Block044Part012
    + surrogateDiagTailX0RatChunk001Sub001Block044Part013
    + surrogateDiagTailX0RatChunk001Sub001Block044Part014
    + surrogateDiagTailX0RatChunk001Sub001Block044Part015
    + surrogateDiagTailX0RatChunk001Sub001Block044Part016
    + surrogateDiagTailX0RatChunk001Sub001Block044Part017
    + surrogateDiagTailX0RatChunk001Sub001Block044Part018
    + surrogateDiagTailX0RatChunk001Sub001Block044Part019

def surrogateDiagonalTailChunk001Sub001Block044TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block044Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block044Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block044Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block044Part020
    + surrogateDiagTailX0RatChunk001Sub001Block044Part021
    + surrogateDiagTailX0RatChunk001Sub001Block044Part022
    + surrogateDiagTailX0RatChunk001Sub001Block044Part023
    + surrogateDiagTailX0RatChunk001Sub001Block044Part024

def surrogateDiagonalTailChunk001Sub001Block044Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block044HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block044MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block044TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block044 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block044Part000
    + surrogateDiagTailX0RatChunk001Sub001Block044Part001
    + surrogateDiagTailX0RatChunk001Sub001Block044Part002
    + surrogateDiagTailX0RatChunk001Sub001Block044Part003
    + surrogateDiagTailX0RatChunk001Sub001Block044Part004
    + surrogateDiagTailX0RatChunk001Sub001Block044Part005
    + surrogateDiagTailX0RatChunk001Sub001Block044Part006
    + surrogateDiagTailX0RatChunk001Sub001Block044Part007
    + surrogateDiagTailX0RatChunk001Sub001Block044Part008
    + surrogateDiagTailX0RatChunk001Sub001Block044Part009
    + surrogateDiagTailX0RatChunk001Sub001Block044Part010
    + surrogateDiagTailX0RatChunk001Sub001Block044Part011
    + surrogateDiagTailX0RatChunk001Sub001Block044Part012
    + surrogateDiagTailX0RatChunk001Sub001Block044Part013
    + surrogateDiagTailX0RatChunk001Sub001Block044Part014
    + surrogateDiagTailX0RatChunk001Sub001Block044Part015
    + surrogateDiagTailX0RatChunk001Sub001Block044Part016
    + surrogateDiagTailX0RatChunk001Sub001Block044Part017
    + surrogateDiagTailX0RatChunk001Sub001Block044Part018
    + surrogateDiagTailX0RatChunk001Sub001Block044Part019
    + surrogateDiagTailX0RatChunk001Sub001Block044Part020
    + surrogateDiagTailX0RatChunk001Sub001Block044Part021
    + surrogateDiagTailX0RatChunk001Sub001Block044Part022
    + surrogateDiagTailX0RatChunk001Sub001Block044Part023
    + surrogateDiagTailX0RatChunk001Sub001Block044Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block044_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block044Head + surrogateDiagTailX0RatChunk001Sub001Block044Mid + surrogateDiagTailX0RatChunk001Sub001Block044Tail =
      surrogateDiagTailX0RatChunk001Sub001Block044 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block044Head surrogateDiagTailX0RatChunk001Sub001Block044Mid surrogateDiagTailX0RatChunk001Sub001Block044Tail surrogateDiagTailX0RatChunk001Sub001Block044
  ring

def SurrogateDiagonalTailChunk001Sub001Block044HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block044HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block044Head

def SurrogateDiagonalTailChunk001Sub001Block044MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block044MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block044Mid

def SurrogateDiagonalTailChunk001Sub001Block044TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block044TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block044Tail

theorem surrogateDiagonalTailChunk001Sub001Block044_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block044HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block044MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block044TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block044Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block044 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block044HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block044MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block044TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block044Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block044_eq_head_add_mid_add_tail

/-- Block 045 covers tail-support indices [16125,16150) and q from 26578 to 26615. -/

def TailChunk001Sub001Block045Part000SupportExplicit : Finset ℕ :=
  ([26578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part000 : ℚ :=
  (157739768675 : ℚ) / 1068460599605723136

def SurrogateDiagonalTailChunk001Sub001Block045Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26578
    = surrogateDiagTailX0RatChunk001Sub001Block045Part000

theorem surrogateDiagonalTailChunk001Sub001Block045Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part000] using hcert

def TailChunk001Sub001Block045Part001SupportExplicit : Finset ℕ :=
  ([26579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part001 : ℚ :=
  (69421226125 : ℚ) / 51759887429547288576

def SurrogateDiagonalTailChunk001Sub001Block045Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26579
    = surrogateDiagTailX0RatChunk001Sub001Block045Part001

theorem surrogateDiagonalTailChunk001Sub001Block045Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part001] using hcert

def TailChunk001Sub001Block045Part002SupportExplicit : Finset ℕ :=
  ([26581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part002 : ℚ :=
  (371927086375 : ℚ) / 1002641242695395937408

def SurrogateDiagonalTailChunk001Sub001Block045Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26581
    = surrogateDiagTailX0RatChunk001Sub001Block045Part002

theorem surrogateDiagonalTailChunk001Sub001Block045Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part002] using hcert

def TailChunk001Sub001Block045Part003SupportExplicit : Finset ℕ :=
  ([26582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block045Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26582
    = surrogateDiagTailX0RatChunk001Sub001Block045Part003

theorem surrogateDiagonalTailChunk001Sub001Block045Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part003] using hcert

def TailChunk001Sub001Block045Part004SupportExplicit : Finset ℕ :=
  ([26583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part004 : ℚ :=
  (5001 : ℚ) / 1971899904051200

def SurrogateDiagonalTailChunk001Sub001Block045Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26583
    = surrogateDiagTailX0RatChunk001Sub001Block045Part004

theorem surrogateDiagonalTailChunk001Sub001Block045Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part004] using hcert

def TailChunk001Sub001Block045Part005SupportExplicit : Finset ℕ :=
  ([26585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part005 : ℚ :=
  (150687358325 : ℚ) / 122605853804756729856

def SurrogateDiagonalTailChunk001Sub001Block045Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26585
    = surrogateDiagTailX0RatChunk001Sub001Block045Part005

theorem surrogateDiagonalTailChunk001Sub001Block045Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part005] using hcert

def TailChunk001Sub001Block045Part006SupportExplicit : Finset ℕ :=
  ([26587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part006 : ℚ :=
  (7326137239 : ℚ) / 8519509247921356800

def SurrogateDiagonalTailChunk001Sub001Block045Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26587
    = surrogateDiagTailX0RatChunk001Sub001Block045Part006

theorem surrogateDiagonalTailChunk001Sub001Block045Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part006] using hcert

def TailChunk001Sub001Block045Part007SupportExplicit : Finset ℕ :=
  ([26589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part007 : ℚ :=
  (41675 : ℚ) / 16447341696218496

def SurrogateDiagonalTailChunk001Sub001Block045Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26589
    = surrogateDiagTailX0RatChunk001Sub001Block045Part007

theorem surrogateDiagonalTailChunk001Sub001Block045Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part007] using hcert

def TailChunk001Sub001Block045Part008SupportExplicit : Finset ℕ :=
  ([26590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part008 : ℚ :=
  (442811105125 : ℚ) / 31951167401318565888

def SurrogateDiagonalTailChunk001Sub001Block045Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26590
    = surrogateDiagTailX0RatChunk001Sub001Block045Part008

theorem surrogateDiagonalTailChunk001Sub001Block045Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part008] using hcert

def TailChunk001Sub001Block045Part009SupportExplicit : Finset ℕ :=
  ([26591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block045Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26591
    = surrogateDiagTailX0RatChunk001Sub001Block045Part009

theorem surrogateDiagonalTailChunk001Sub001Block045Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part009] using hcert

def TailChunk001Sub001Block045Part010SupportExplicit : Finset ℕ :=
  ([26593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part010 : ℚ :=
  (44137882471 : ℚ) / 22756076565988147200

def SurrogateDiagonalTailChunk001Sub001Block045Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26593
    = surrogateDiagTailX0RatChunk001Sub001Block045Part010

theorem surrogateDiagonalTailChunk001Sub001Block045Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part010] using hcert

def TailChunk001Sub001Block045Part011SupportExplicit : Finset ℕ :=
  ([26594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block045Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26594
    = surrogateDiagTailX0RatChunk001Sub001Block045Part011

theorem surrogateDiagonalTailChunk001Sub001Block045Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part011] using hcert

def TailChunk001Sub001Block045Part012SupportExplicit : Finset ℕ :=
  ([26597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block045Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26597
    = surrogateDiagTailX0RatChunk001Sub001Block045Part012

theorem surrogateDiagonalTailChunk001Sub001Block045Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part012] using hcert

def TailChunk001Sub001Block045Part013SupportExplicit : Finset ℕ :=
  ([26598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part013 : ℚ :=
  (16689801259 : ℚ) / 89597435904000000

def SurrogateDiagonalTailChunk001Sub001Block045Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26598
    = surrogateDiagTailX0RatChunk001Sub001Block045Part013

theorem surrogateDiagonalTailChunk001Sub001Block045Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part013] using hcert

def TailChunk001Sub001Block045Part014SupportExplicit : Finset ℕ :=
  ([26599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part014 : ℚ :=
  (6719653975 : ℚ) / 53034766846667172864

def SurrogateDiagonalTailChunk001Sub001Block045Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26599
    = surrogateDiagTailX0RatChunk001Sub001Block045Part014

theorem surrogateDiagonalTailChunk001Sub001Block045Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part014] using hcert

def TailChunk001Sub001Block045Part015SupportExplicit : Finset ℕ :=
  ([26601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part015 : ℚ :=
  (125025 : ℚ) / 49431170549391488

def SurrogateDiagonalTailChunk001Sub001Block045Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26601
    = surrogateDiagTailX0RatChunk001Sub001Block045Part015

theorem surrogateDiagonalTailChunk001Sub001Block045Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part015] using hcert

def TailChunk001Sub001Block045Part016SupportExplicit : Finset ℕ :=
  ([26602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part016 : ℚ :=
  (51743312375 : ℚ) / 35401741226347097664

def SurrogateDiagonalTailChunk001Sub001Block045Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26602
    = surrogateDiagTailX0RatChunk001Sub001Block045Part016

theorem surrogateDiagonalTailChunk001Sub001Block045Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part016] using hcert

def TailChunk001Sub001Block045Part017SupportExplicit : Finset ℕ :=
  ([26603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part017 : ℚ :=
  (236511909475 : ℚ) / 1116181034392971921408

def SurrogateDiagonalTailChunk001Sub001Block045Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26603
    = surrogateDiagTailX0RatChunk001Sub001Block045Part017

theorem surrogateDiagonalTailChunk001Sub001Block045Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part017] using hcert

def TailChunk001Sub001Block045Part018SupportExplicit : Finset ℕ :=
  ([26605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part018 : ℚ :=
  (485659736275 : ℚ) / 99381406669127811072

def SurrogateDiagonalTailChunk001Sub001Block045Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26605
    = surrogateDiagTailX0RatChunk001Sub001Block045Part018

theorem surrogateDiagonalTailChunk001Sub001Block045Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part018] using hcert

def TailChunk001Sub001Block045Part019SupportExplicit : Finset ℕ :=
  ([26606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part019 : ℚ :=
  (1204119243 : ℚ) / 952223740000000000

def SurrogateDiagonalTailChunk001Sub001Block045Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26606
    = surrogateDiagTailX0RatChunk001Sub001Block045Part019

theorem surrogateDiagonalTailChunk001Sub001Block045Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part019] using hcert

def TailChunk001Sub001Block045Part020SupportExplicit : Finset ℕ :=
  ([26609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part020 : ℚ :=
  (490276811 : ℚ) / 362200297574400000

def SurrogateDiagonalTailChunk001Sub001Block045Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26609
    = surrogateDiagTailX0RatChunk001Sub001Block045Part020

theorem surrogateDiagonalTailChunk001Sub001Block045Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part020] using hcert

def TailChunk001Sub001Block045Part021SupportExplicit : Finset ℕ :=
  ([26610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part021 : ℚ :=
  (442399955175 : ℚ) / 2103780569634144256

def SurrogateDiagonalTailChunk001Sub001Block045Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26610
    = surrogateDiagTailX0RatChunk001Sub001Block045Part021

theorem surrogateDiagonalTailChunk001Sub001Block045Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part021] using hcert

def TailChunk001Sub001Block045Part022SupportExplicit : Finset ℕ :=
  ([26611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part022 : ℚ :=
  (141879333775 : ℚ) / 121400927452290613248

def SurrogateDiagonalTailChunk001Sub001Block045Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26611
    = surrogateDiagTailX0RatChunk001Sub001Block045Part022

theorem surrogateDiagonalTailChunk001Sub001Block045Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part022] using hcert

def TailChunk001Sub001Block045Part023SupportExplicit : Finset ℕ :=
  ([26614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part023 : ℚ :=
  (9060690647 : ℚ) / 844648976016000000

def SurrogateDiagonalTailChunk001Sub001Block045Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26614
    = surrogateDiagTailX0RatChunk001Sub001Block045Part023

theorem surrogateDiagonalTailChunk001Sub001Block045Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part023] using hcert

def TailChunk001Sub001Block045Part024SupportExplicit : Finset ℕ :=
  ([26615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block045Part024 : ℚ :=
  (1771480772125 : ℚ) / 513530573790030317568

def SurrogateDiagonalTailChunk001Sub001Block045Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26615
    = surrogateDiagTailX0RatChunk001Sub001Block045Part024

theorem surrogateDiagonalTailChunk001Sub001Block045Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block045Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block045Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block045Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block045Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block045Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block045HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block045Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block045Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block045Part000
    + surrogateDiagTailX0RatChunk001Sub001Block045Part001
    + surrogateDiagTailX0RatChunk001Sub001Block045Part002
    + surrogateDiagTailX0RatChunk001Sub001Block045Part003
    + surrogateDiagTailX0RatChunk001Sub001Block045Part004
    + surrogateDiagTailX0RatChunk001Sub001Block045Part005
    + surrogateDiagTailX0RatChunk001Sub001Block045Part006
    + surrogateDiagTailX0RatChunk001Sub001Block045Part007
    + surrogateDiagTailX0RatChunk001Sub001Block045Part008
    + surrogateDiagTailX0RatChunk001Sub001Block045Part009

def surrogateDiagonalTailChunk001Sub001Block045MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block045Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block045Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block045Part010
    + surrogateDiagTailX0RatChunk001Sub001Block045Part011
    + surrogateDiagTailX0RatChunk001Sub001Block045Part012
    + surrogateDiagTailX0RatChunk001Sub001Block045Part013
    + surrogateDiagTailX0RatChunk001Sub001Block045Part014
    + surrogateDiagTailX0RatChunk001Sub001Block045Part015
    + surrogateDiagTailX0RatChunk001Sub001Block045Part016
    + surrogateDiagTailX0RatChunk001Sub001Block045Part017
    + surrogateDiagTailX0RatChunk001Sub001Block045Part018
    + surrogateDiagTailX0RatChunk001Sub001Block045Part019

def surrogateDiagonalTailChunk001Sub001Block045TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block045Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block045Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block045Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block045Part020
    + surrogateDiagTailX0RatChunk001Sub001Block045Part021
    + surrogateDiagTailX0RatChunk001Sub001Block045Part022
    + surrogateDiagTailX0RatChunk001Sub001Block045Part023
    + surrogateDiagTailX0RatChunk001Sub001Block045Part024

def surrogateDiagonalTailChunk001Sub001Block045Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block045HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block045MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block045TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block045 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block045Part000
    + surrogateDiagTailX0RatChunk001Sub001Block045Part001
    + surrogateDiagTailX0RatChunk001Sub001Block045Part002
    + surrogateDiagTailX0RatChunk001Sub001Block045Part003
    + surrogateDiagTailX0RatChunk001Sub001Block045Part004
    + surrogateDiagTailX0RatChunk001Sub001Block045Part005
    + surrogateDiagTailX0RatChunk001Sub001Block045Part006
    + surrogateDiagTailX0RatChunk001Sub001Block045Part007
    + surrogateDiagTailX0RatChunk001Sub001Block045Part008
    + surrogateDiagTailX0RatChunk001Sub001Block045Part009
    + surrogateDiagTailX0RatChunk001Sub001Block045Part010
    + surrogateDiagTailX0RatChunk001Sub001Block045Part011
    + surrogateDiagTailX0RatChunk001Sub001Block045Part012
    + surrogateDiagTailX0RatChunk001Sub001Block045Part013
    + surrogateDiagTailX0RatChunk001Sub001Block045Part014
    + surrogateDiagTailX0RatChunk001Sub001Block045Part015
    + surrogateDiagTailX0RatChunk001Sub001Block045Part016
    + surrogateDiagTailX0RatChunk001Sub001Block045Part017
    + surrogateDiagTailX0RatChunk001Sub001Block045Part018
    + surrogateDiagTailX0RatChunk001Sub001Block045Part019
    + surrogateDiagTailX0RatChunk001Sub001Block045Part020
    + surrogateDiagTailX0RatChunk001Sub001Block045Part021
    + surrogateDiagTailX0RatChunk001Sub001Block045Part022
    + surrogateDiagTailX0RatChunk001Sub001Block045Part023
    + surrogateDiagTailX0RatChunk001Sub001Block045Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block045_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block045Head + surrogateDiagTailX0RatChunk001Sub001Block045Mid + surrogateDiagTailX0RatChunk001Sub001Block045Tail =
      surrogateDiagTailX0RatChunk001Sub001Block045 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block045Head surrogateDiagTailX0RatChunk001Sub001Block045Mid surrogateDiagTailX0RatChunk001Sub001Block045Tail surrogateDiagTailX0RatChunk001Sub001Block045
  ring

def SurrogateDiagonalTailChunk001Sub001Block045HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block045HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block045Head

def SurrogateDiagonalTailChunk001Sub001Block045MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block045MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block045Mid

def SurrogateDiagonalTailChunk001Sub001Block045TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block045TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block045Tail

theorem surrogateDiagonalTailChunk001Sub001Block045_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block045HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block045MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block045TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block045Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block045 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block045HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block045MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block045TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block045Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block045_eq_head_add_mid_add_tail

/-- Block 046 covers tail-support indices [16150,16175) and q from 26617 to 26657. -/

def TailChunk001Sub001Block046Part000SupportExplicit : Finset ℕ :=
  ([26617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part000 : ℚ :=
  (101948289575 : ℚ) / 567476557067655273024

def SurrogateDiagonalTailChunk001Sub001Block046Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26617
    = surrogateDiagTailX0RatChunk001Sub001Block046Part000

theorem surrogateDiagonalTailChunk001Sub001Block046Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part000] using hcert

def TailChunk001Sub001Block046Part001SupportExplicit : Finset ℕ :=
  ([26618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26618
    = surrogateDiagTailX0RatChunk001Sub001Block046Part001

theorem surrogateDiagonalTailChunk001Sub001Block046Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part001] using hcert

def TailChunk001Sub001Block046Part002SupportExplicit : Finset ℕ :=
  ([26619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part002 : ℚ :=
  (1684822825 : ℚ) / 1031523912238061664

def SurrogateDiagonalTailChunk001Sub001Block046Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26619
    = surrogateDiagTailX0RatChunk001Sub001Block046Part002

theorem surrogateDiagonalTailChunk001Sub001Block046Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part002] using hcert

def TailChunk001Sub001Block046Part003SupportExplicit : Finset ℕ :=
  ([26621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part003 : ℚ :=
  (905325189925 : ℚ) / 677142870982333527168

def SurrogateDiagonalTailChunk001Sub001Block046Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26621
    = surrogateDiagTailX0RatChunk001Sub001Block046Part003

theorem surrogateDiagonalTailChunk001Sub001Block046Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part003] using hcert

def TailChunk001Sub001Block046Part004SupportExplicit : Finset ℕ :=
  ([26623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part004 : ℚ :=
  (4807891525 : ℚ) / 43691667006697242624

def SurrogateDiagonalTailChunk001Sub001Block046Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26623
    = surrogateDiagTailX0RatChunk001Sub001Block046Part004

theorem surrogateDiagonalTailChunk001Sub001Block046Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part004] using hcert

def TailChunk001Sub001Block046Part005SupportExplicit : Finset ℕ :=
  ([26626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part005 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26626
    = surrogateDiagTailX0RatChunk001Sub001Block046Part005

theorem surrogateDiagonalTailChunk001Sub001Block046Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part005] using hcert

def TailChunk001Sub001Block046Part006SupportExplicit : Finset ℕ :=
  ([26627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26627
    = surrogateDiagTailX0RatChunk001Sub001Block046Part006

theorem surrogateDiagonalTailChunk001Sub001Block046Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part006] using hcert

def TailChunk001Sub001Block046Part007SupportExplicit : Finset ℕ :=
  ([26629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part007 : ℚ :=
  (1913824433 : ℚ) / 8781142322604263040

def SurrogateDiagonalTailChunk001Sub001Block046Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26629
    = surrogateDiagTailX0RatChunk001Sub001Block046Part007

theorem surrogateDiagonalTailChunk001Sub001Block046Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part007] using hcert

def TailChunk001Sub001Block046Part008SupportExplicit : Finset ℕ :=
  ([26630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part008 : ℚ :=
  (886853670025 : ℚ) / 32143934078938564608

def SurrogateDiagonalTailChunk001Sub001Block046Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26630
    = surrogateDiagTailX0RatChunk001Sub001Block046Part008

theorem surrogateDiagonalTailChunk001Sub001Block046Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part008] using hcert

def TailChunk001Sub001Block046Part009SupportExplicit : Finset ℕ :=
  ([26633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26633
    = surrogateDiagTailX0RatChunk001Sub001Block046Part009

theorem surrogateDiagonalTailChunk001Sub001Block046Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part009] using hcert

def TailChunk001Sub001Block046Part010SupportExplicit : Finset ℕ :=
  ([26634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part010 : ℚ :=
  (624295498925 : ℚ) / 6368138261277179904

def SurrogateDiagonalTailChunk001Sub001Block046Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26634
    = surrogateDiagTailX0RatChunk001Sub001Block046Part010

theorem surrogateDiagonalTailChunk001Sub001Block046Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part010] using hcert

def TailChunk001Sub001Block046Part011SupportExplicit : Finset ℕ :=
  ([26635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part011 : ℚ :=
  (375786377 : ℚ) / 51254551196467200

def SurrogateDiagonalTailChunk001Sub001Block046Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26635
    = surrogateDiagTailX0RatChunk001Sub001Block046Part011

theorem surrogateDiagonalTailChunk001Sub001Block046Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part011] using hcert

def TailChunk001Sub001Block046Part012SupportExplicit : Finset ℕ :=
  ([26637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part012 : ℚ :=
  (32123460575 : ℚ) / 14956434669985357824

def SurrogateDiagonalTailChunk001Sub001Block046Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26637
    = surrogateDiagTailX0RatChunk001Sub001Block046Part012

theorem surrogateDiagonalTailChunk001Sub001Block046Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part012] using hcert

def TailChunk001Sub001Block046Part013SupportExplicit : Finset ℕ :=
  ([26638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part013 : ℚ :=
  (8789597767 : ℚ) / 2520977854752000000

def SurrogateDiagonalTailChunk001Sub001Block046Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26638
    = surrogateDiagTailX0RatChunk001Sub001Block046Part013

theorem surrogateDiagonalTailChunk001Sub001Block046Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part013] using hcert

def TailChunk001Sub001Block046Part014SupportExplicit : Finset ℕ :=
  ([26639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part014 : ℚ :=
  (12906439525 : ℚ) / 27376083675482554368

def SurrogateDiagonalTailChunk001Sub001Block046Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26639
    = surrogateDiagTailX0RatChunk001Sub001Block046Part014

theorem surrogateDiagonalTailChunk001Sub001Block046Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part014] using hcert

def TailChunk001Sub001Block046Part015SupportExplicit : Finset ℕ :=
  ([26641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26641
    = surrogateDiagTailX0RatChunk001Sub001Block046Part015

theorem surrogateDiagonalTailChunk001Sub001Block046Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part015] using hcert

def TailChunk001Sub001Block046Part016SupportExplicit : Finset ℕ :=
  ([26642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part016 : ℚ :=
  (2099341079 : ℚ) / 63027943100006400

def SurrogateDiagonalTailChunk001Sub001Block046Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26642
    = surrogateDiagTailX0RatChunk001Sub001Block046Part016

theorem surrogateDiagonalTailChunk001Sub001Block046Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part016] using hcert

def TailChunk001Sub001Block046Part017SupportExplicit : Finset ℕ :=
  ([26643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part017 : ℚ :=
  (117778845475 : ℚ) / 228362985510269011968

def SurrogateDiagonalTailChunk001Sub001Block046Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26643
    = surrogateDiagTailX0RatChunk001Sub001Block046Part017

theorem surrogateDiagonalTailChunk001Sub001Block046Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part017] using hcert

def TailChunk001Sub001Block046Part018SupportExplicit : Finset ℕ :=
  ([26646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part018 : ℚ :=
  (2465450153 : ℚ) / 31096300013199360

def SurrogateDiagonalTailChunk001Sub001Block046Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26646
    = surrogateDiagTailX0RatChunk001Sub001Block046Part018

theorem surrogateDiagonalTailChunk001Sub001Block046Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part018] using hcert

def TailChunk001Sub001Block046Part019SupportExplicit : Finset ℕ :=
  ([26647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26647
    = surrogateDiagTailX0RatChunk001Sub001Block046Part019

theorem surrogateDiagonalTailChunk001Sub001Block046Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part019] using hcert

def TailChunk001Sub001Block046Part020SupportExplicit : Finset ℕ :=
  ([26651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part020 : ℚ :=
  (67968183025 : ℚ) / 272878750463137362432

def SurrogateDiagonalTailChunk001Sub001Block046Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26651
    = surrogateDiagTailX0RatChunk001Sub001Block046Part020

theorem surrogateDiagonalTailChunk001Sub001Block046Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part020] using hcert

def TailChunk001Sub001Block046Part021SupportExplicit : Finset ℕ :=
  ([26653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part021 : ℚ :=
  (1840603741 : ℚ) / 2151113980209688200

def SurrogateDiagonalTailChunk001Sub001Block046Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26653
    = surrogateDiagTailX0RatChunk001Sub001Block046Part021

theorem surrogateDiagonalTailChunk001Sub001Block046Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part021] using hcert

def TailChunk001Sub001Block046Part022SupportExplicit : Finset ℕ :=
  ([26654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block046Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26654
    = surrogateDiagTailX0RatChunk001Sub001Block046Part022

theorem surrogateDiagonalTailChunk001Sub001Block046Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part022] using hcert

def TailChunk001Sub001Block046Part023SupportExplicit : Finset ℕ :=
  ([26655] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part023 : ℚ :=
  (296388202975 : ℚ) / 25474088970812915712

def SurrogateDiagonalTailChunk001Sub001Block046Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26655
    = surrogateDiagTailX0RatChunk001Sub001Block046Part023

theorem surrogateDiagonalTailChunk001Sub001Block046Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part023] using hcert

def TailChunk001Sub001Block046Part024SupportExplicit : Finset ℕ :=
  ([26657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block046Part024 : ℚ :=
  (5029403189 : ℚ) / 5312774039235379200

def SurrogateDiagonalTailChunk001Sub001Block046Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26657
    = surrogateDiagTailX0RatChunk001Sub001Block046Part024

theorem surrogateDiagonalTailChunk001Sub001Block046Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block046Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block046Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block046Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block046Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block046Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block046HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block046Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block046Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block046Part000
    + surrogateDiagTailX0RatChunk001Sub001Block046Part001
    + surrogateDiagTailX0RatChunk001Sub001Block046Part002
    + surrogateDiagTailX0RatChunk001Sub001Block046Part003
    + surrogateDiagTailX0RatChunk001Sub001Block046Part004
    + surrogateDiagTailX0RatChunk001Sub001Block046Part005
    + surrogateDiagTailX0RatChunk001Sub001Block046Part006
    + surrogateDiagTailX0RatChunk001Sub001Block046Part007
    + surrogateDiagTailX0RatChunk001Sub001Block046Part008
    + surrogateDiagTailX0RatChunk001Sub001Block046Part009

def surrogateDiagonalTailChunk001Sub001Block046MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block046Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block046Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block046Part010
    + surrogateDiagTailX0RatChunk001Sub001Block046Part011
    + surrogateDiagTailX0RatChunk001Sub001Block046Part012
    + surrogateDiagTailX0RatChunk001Sub001Block046Part013
    + surrogateDiagTailX0RatChunk001Sub001Block046Part014
    + surrogateDiagTailX0RatChunk001Sub001Block046Part015
    + surrogateDiagTailX0RatChunk001Sub001Block046Part016
    + surrogateDiagTailX0RatChunk001Sub001Block046Part017
    + surrogateDiagTailX0RatChunk001Sub001Block046Part018
    + surrogateDiagTailX0RatChunk001Sub001Block046Part019

def surrogateDiagonalTailChunk001Sub001Block046TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block046Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block046Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block046Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block046Part020
    + surrogateDiagTailX0RatChunk001Sub001Block046Part021
    + surrogateDiagTailX0RatChunk001Sub001Block046Part022
    + surrogateDiagTailX0RatChunk001Sub001Block046Part023
    + surrogateDiagTailX0RatChunk001Sub001Block046Part024

def surrogateDiagonalTailChunk001Sub001Block046Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block046HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block046MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block046TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block046 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block046Part000
    + surrogateDiagTailX0RatChunk001Sub001Block046Part001
    + surrogateDiagTailX0RatChunk001Sub001Block046Part002
    + surrogateDiagTailX0RatChunk001Sub001Block046Part003
    + surrogateDiagTailX0RatChunk001Sub001Block046Part004
    + surrogateDiagTailX0RatChunk001Sub001Block046Part005
    + surrogateDiagTailX0RatChunk001Sub001Block046Part006
    + surrogateDiagTailX0RatChunk001Sub001Block046Part007
    + surrogateDiagTailX0RatChunk001Sub001Block046Part008
    + surrogateDiagTailX0RatChunk001Sub001Block046Part009
    + surrogateDiagTailX0RatChunk001Sub001Block046Part010
    + surrogateDiagTailX0RatChunk001Sub001Block046Part011
    + surrogateDiagTailX0RatChunk001Sub001Block046Part012
    + surrogateDiagTailX0RatChunk001Sub001Block046Part013
    + surrogateDiagTailX0RatChunk001Sub001Block046Part014
    + surrogateDiagTailX0RatChunk001Sub001Block046Part015
    + surrogateDiagTailX0RatChunk001Sub001Block046Part016
    + surrogateDiagTailX0RatChunk001Sub001Block046Part017
    + surrogateDiagTailX0RatChunk001Sub001Block046Part018
    + surrogateDiagTailX0RatChunk001Sub001Block046Part019
    + surrogateDiagTailX0RatChunk001Sub001Block046Part020
    + surrogateDiagTailX0RatChunk001Sub001Block046Part021
    + surrogateDiagTailX0RatChunk001Sub001Block046Part022
    + surrogateDiagTailX0RatChunk001Sub001Block046Part023
    + surrogateDiagTailX0RatChunk001Sub001Block046Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block046_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block046Head + surrogateDiagTailX0RatChunk001Sub001Block046Mid + surrogateDiagTailX0RatChunk001Sub001Block046Tail =
      surrogateDiagTailX0RatChunk001Sub001Block046 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block046Head surrogateDiagTailX0RatChunk001Sub001Block046Mid surrogateDiagTailX0RatChunk001Sub001Block046Tail surrogateDiagTailX0RatChunk001Sub001Block046
  ring

def SurrogateDiagonalTailChunk001Sub001Block046HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block046HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block046Head

def SurrogateDiagonalTailChunk001Sub001Block046MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block046MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block046Mid

def SurrogateDiagonalTailChunk001Sub001Block046TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block046TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block046Tail

theorem surrogateDiagonalTailChunk001Sub001Block046_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block046HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block046MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block046TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block046Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block046 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block046HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block046MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block046TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block046Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block046_eq_head_add_mid_add_tail

/-- Block 047 covers tail-support indices [16175,16200) and q from 26659 to 26697. -/

def TailChunk001Sub001Block047Part000SupportExplicit : Finset ℕ :=
  ([26659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part000 : ℚ :=
  (78942450575 : ℚ) / 580530586399252030464

def SurrogateDiagonalTailChunk001Sub001Block047Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26659
    = surrogateDiagTailX0RatChunk001Sub001Block047Part000

theorem surrogateDiagonalTailChunk001Sub001Block047Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part000] using hcert

def TailChunk001Sub001Block047Part001SupportExplicit : Finset ℕ :=
  ([26661] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part001 : ℚ :=
  (41675 : ℚ) / 16626237038165376

def SurrogateDiagonalTailChunk001Sub001Block047Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26661
    = surrogateDiagTailX0RatChunk001Sub001Block047Part001

theorem surrogateDiagonalTailChunk001Sub001Block047Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part001] using hcert

def TailChunk001Sub001Block047Part002SupportExplicit : Finset ℕ :=
  ([26662] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26662
    = surrogateDiagTailX0RatChunk001Sub001Block047Part002

theorem surrogateDiagonalTailChunk001Sub001Block047Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part002] using hcert

def TailChunk001Sub001Block047Part003SupportExplicit : Finset ℕ :=
  ([26663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part003 : ℚ :=
  (358666233625 : ℚ) / 122131659733624553472

def SurrogateDiagonalTailChunk001Sub001Block047Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26663
    = surrogateDiagTailX0RatChunk001Sub001Block047Part003

theorem surrogateDiagonalTailChunk001Sub001Block047Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part003] using hcert

def TailChunk001Sub001Block047Part004SupportExplicit : Finset ℕ :=
  ([26665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part004 : ℚ :=
  (592713173625 : ℚ) / 172467049006402994176

def SurrogateDiagonalTailChunk001Sub001Block047Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26665
    = surrogateDiagTailX0RatChunk001Sub001Block047Part004

theorem surrogateDiagonalTailChunk001Sub001Block047Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part004] using hcert

def TailChunk001Sub001Block047Part005SupportExplicit : Finset ℕ :=
  ([26666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part005 : ℚ :=
  (40842666875 : ℚ) / 36461402207083681344

def SurrogateDiagonalTailChunk001Sub001Block047Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26666
    = surrogateDiagTailX0RatChunk001Sub001Block047Part005

theorem surrogateDiagonalTailChunk001Sub001Block047Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part005] using hcert

def TailChunk001Sub001Block047Part006SupportExplicit : Finset ℕ :=
  ([26669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26669
    = surrogateDiagTailX0RatChunk001Sub001Block047Part006

theorem surrogateDiagonalTailChunk001Sub001Block047Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part006] using hcert

def TailChunk001Sub001Block047Part007SupportExplicit : Finset ℕ :=
  ([26670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part007 : ℚ :=
  (1282984978525 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk001Sub001Block047Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26670
    = surrogateDiagTailX0RatChunk001Sub001Block047Part007

theorem surrogateDiagonalTailChunk001Sub001Block047Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part007] using hcert

def TailChunk001Sub001Block047Part008SupportExplicit : Finset ℕ :=
  ([26671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part008 : ℚ :=
  (101999948725 : ℚ) / 1204352808417566312448

def SurrogateDiagonalTailChunk001Sub001Block047Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26671
    = surrogateDiagTailX0RatChunk001Sub001Block047Part008

theorem surrogateDiagonalTailChunk001Sub001Block047Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part008] using hcert

def TailChunk001Sub001Block047Part009SupportExplicit : Finset ℕ :=
  ([26673] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part009 : ℚ :=
  (10551325 : ℚ) / 6487848190476288

def SurrogateDiagonalTailChunk001Sub001Block047Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26673
    = surrogateDiagTailX0RatChunk001Sub001Block047Part009

theorem surrogateDiagonalTailChunk001Sub001Block047Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part009] using hcert

def TailChunk001Sub001Block047Part010SupportExplicit : Finset ℕ :=
  ([26674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26674
    = surrogateDiagTailX0RatChunk001Sub001Block047Part010

theorem surrogateDiagonalTailChunk001Sub001Block047Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part010] using hcert

def TailChunk001Sub001Block047Part011SupportExplicit : Finset ℕ :=
  ([26677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part011 : ℚ :=
  (40709533475 : ℚ) / 21821207867106361344

def SurrogateDiagonalTailChunk001Sub001Block047Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26677
    = surrogateDiagTailX0RatChunk001Sub001Block047Part011

theorem surrogateDiagonalTailChunk001Sub001Block047Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part011] using hcert

def TailChunk001Sub001Block047Part012SupportExplicit : Finset ℕ :=
  ([26678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26678
    = surrogateDiagTailX0RatChunk001Sub001Block047Part012

theorem surrogateDiagonalTailChunk001Sub001Block047Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part012] using hcert

def TailChunk001Sub001Block047Part013SupportExplicit : Finset ℕ :=
  ([26679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part013 : ℚ :=
  (41675 : ℚ) / 16671187974445056

def SurrogateDiagonalTailChunk001Sub001Block047Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26679
    = surrogateDiagTailX0RatChunk001Sub001Block047Part013

theorem surrogateDiagonalTailChunk001Sub001Block047Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part013] using hcert

def TailChunk001Sub001Block047Part014SupportExplicit : Finset ℕ :=
  ([26681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26681
    = surrogateDiagTailX0RatChunk001Sub001Block047Part014

theorem surrogateDiagonalTailChunk001Sub001Block047Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part014] using hcert

def TailChunk001Sub001Block047Part015SupportExplicit : Finset ℕ :=
  ([26682] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part015 : ℚ :=
  (618028663175 : ℚ) / 7816182286893724224

def SurrogateDiagonalTailChunk001Sub001Block047Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26682
    = surrogateDiagTailX0RatChunk001Sub001Block047Part015

theorem surrogateDiagonalTailChunk001Sub001Block047Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part015] using hcert

def TailChunk001Sub001Block047Part016SupportExplicit : Finset ℕ :=
  ([26683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26683
    = surrogateDiagTailX0RatChunk001Sub001Block047Part016

theorem surrogateDiagonalTailChunk001Sub001Block047Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part016] using hcert

def TailChunk001Sub001Block047Part017SupportExplicit : Finset ℕ :=
  ([26686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part017 : ℚ :=
  (14805717541 : ℚ) / 2158228034431027200

def SurrogateDiagonalTailChunk001Sub001Block047Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26686
    = surrogateDiagTailX0RatChunk001Sub001Block047Part017

theorem surrogateDiagonalTailChunk001Sub001Block047Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part017] using hcert

def TailChunk001Sub001Block047Part018SupportExplicit : Finset ℕ :=
  ([26687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26687
    = surrogateDiagTailX0RatChunk001Sub001Block047Part018

theorem surrogateDiagonalTailChunk001Sub001Block047Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part018] using hcert

def TailChunk001Sub001Block047Part019SupportExplicit : Finset ℕ :=
  ([26689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part019 : ℚ :=
  (6543040025 : ℚ) / 11349487476000718848

def SurrogateDiagonalTailChunk001Sub001Block047Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26689
    = surrogateDiagTailX0RatChunk001Sub001Block047Part019

theorem surrogateDiagonalTailChunk001Sub001Block047Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part019] using hcert

def TailChunk001Sub001Block047Part020SupportExplicit : Finset ℕ :=
  ([26690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part020 : ℚ :=
  (1003864996525 : ℚ) / 24845351667281952768

def SurrogateDiagonalTailChunk001Sub001Block047Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26690
    = surrogateDiagTailX0RatChunk001Sub001Block047Part020

theorem surrogateDiagonalTailChunk001Sub001Block047Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part020] using hcert

def TailChunk001Sub001Block047Part021SupportExplicit : Finset ℕ :=
  ([26691] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part021 : ℚ :=
  (7072756937 : ℚ) / 860135384678400000

def SurrogateDiagonalTailChunk001Sub001Block047Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26691
    = surrogateDiagTailX0RatChunk001Sub001Block047Part021

theorem surrogateDiagonalTailChunk001Sub001Block047Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part021] using hcert

def TailChunk001Sub001Block047Part022SupportExplicit : Finset ℕ :=
  ([26693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block047Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26693
    = surrogateDiagTailX0RatChunk001Sub001Block047Part022

theorem surrogateDiagonalTailChunk001Sub001Block047Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part022] using hcert

def TailChunk001Sub001Block047Part023SupportExplicit : Finset ℕ :=
  ([26695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part023 : ℚ :=
  (19871526163 : ℚ) / 4130370117225676800

def SurrogateDiagonalTailChunk001Sub001Block047Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26695
    = surrogateDiagTailX0RatChunk001Sub001Block047Part023

theorem surrogateDiagonalTailChunk001Sub001Block047Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part023] using hcert

def TailChunk001Sub001Block047Part024SupportExplicit : Finset ℕ :=
  ([26697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block047Part024 : ℚ :=
  (19840334713 : ℚ) / 6821066380423987200

def SurrogateDiagonalTailChunk001Sub001Block047Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26697
    = surrogateDiagTailX0RatChunk001Sub001Block047Part024

theorem surrogateDiagonalTailChunk001Sub001Block047Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block047Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block047Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block047Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block047Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block047Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block047HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block047Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block047Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block047Part000
    + surrogateDiagTailX0RatChunk001Sub001Block047Part001
    + surrogateDiagTailX0RatChunk001Sub001Block047Part002
    + surrogateDiagTailX0RatChunk001Sub001Block047Part003
    + surrogateDiagTailX0RatChunk001Sub001Block047Part004
    + surrogateDiagTailX0RatChunk001Sub001Block047Part005
    + surrogateDiagTailX0RatChunk001Sub001Block047Part006
    + surrogateDiagTailX0RatChunk001Sub001Block047Part007
    + surrogateDiagTailX0RatChunk001Sub001Block047Part008
    + surrogateDiagTailX0RatChunk001Sub001Block047Part009

def surrogateDiagonalTailChunk001Sub001Block047MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block047Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block047Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block047Part010
    + surrogateDiagTailX0RatChunk001Sub001Block047Part011
    + surrogateDiagTailX0RatChunk001Sub001Block047Part012
    + surrogateDiagTailX0RatChunk001Sub001Block047Part013
    + surrogateDiagTailX0RatChunk001Sub001Block047Part014
    + surrogateDiagTailX0RatChunk001Sub001Block047Part015
    + surrogateDiagTailX0RatChunk001Sub001Block047Part016
    + surrogateDiagTailX0RatChunk001Sub001Block047Part017
    + surrogateDiagTailX0RatChunk001Sub001Block047Part018
    + surrogateDiagTailX0RatChunk001Sub001Block047Part019

def surrogateDiagonalTailChunk001Sub001Block047TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block047Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block047Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block047Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block047Part020
    + surrogateDiagTailX0RatChunk001Sub001Block047Part021
    + surrogateDiagTailX0RatChunk001Sub001Block047Part022
    + surrogateDiagTailX0RatChunk001Sub001Block047Part023
    + surrogateDiagTailX0RatChunk001Sub001Block047Part024

def surrogateDiagonalTailChunk001Sub001Block047Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block047HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block047MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block047TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block047 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block047Part000
    + surrogateDiagTailX0RatChunk001Sub001Block047Part001
    + surrogateDiagTailX0RatChunk001Sub001Block047Part002
    + surrogateDiagTailX0RatChunk001Sub001Block047Part003
    + surrogateDiagTailX0RatChunk001Sub001Block047Part004
    + surrogateDiagTailX0RatChunk001Sub001Block047Part005
    + surrogateDiagTailX0RatChunk001Sub001Block047Part006
    + surrogateDiagTailX0RatChunk001Sub001Block047Part007
    + surrogateDiagTailX0RatChunk001Sub001Block047Part008
    + surrogateDiagTailX0RatChunk001Sub001Block047Part009
    + surrogateDiagTailX0RatChunk001Sub001Block047Part010
    + surrogateDiagTailX0RatChunk001Sub001Block047Part011
    + surrogateDiagTailX0RatChunk001Sub001Block047Part012
    + surrogateDiagTailX0RatChunk001Sub001Block047Part013
    + surrogateDiagTailX0RatChunk001Sub001Block047Part014
    + surrogateDiagTailX0RatChunk001Sub001Block047Part015
    + surrogateDiagTailX0RatChunk001Sub001Block047Part016
    + surrogateDiagTailX0RatChunk001Sub001Block047Part017
    + surrogateDiagTailX0RatChunk001Sub001Block047Part018
    + surrogateDiagTailX0RatChunk001Sub001Block047Part019
    + surrogateDiagTailX0RatChunk001Sub001Block047Part020
    + surrogateDiagTailX0RatChunk001Sub001Block047Part021
    + surrogateDiagTailX0RatChunk001Sub001Block047Part022
    + surrogateDiagTailX0RatChunk001Sub001Block047Part023
    + surrogateDiagTailX0RatChunk001Sub001Block047Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block047_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block047Head + surrogateDiagTailX0RatChunk001Sub001Block047Mid + surrogateDiagTailX0RatChunk001Sub001Block047Tail =
      surrogateDiagTailX0RatChunk001Sub001Block047 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block047Head surrogateDiagTailX0RatChunk001Sub001Block047Mid surrogateDiagTailX0RatChunk001Sub001Block047Tail surrogateDiagTailX0RatChunk001Sub001Block047
  ring

def SurrogateDiagonalTailChunk001Sub001Block047HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block047HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block047Head

def SurrogateDiagonalTailChunk001Sub001Block047MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block047MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block047Mid

def SurrogateDiagonalTailChunk001Sub001Block047TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block047TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block047Tail

theorem surrogateDiagonalTailChunk001Sub001Block047_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block047HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block047MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block047TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block047Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block047 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block047HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block047MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block047TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block047Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block047_eq_head_add_mid_add_tail

/-- Block 048 covers tail-support indices [16200,16225) and q from 26698 to 26742. -/

def TailChunk001Sub001Block048Part000SupportExplicit : Finset ℕ :=
  ([26698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part000 : ℚ :=
  (227944230875 : ℚ) / 21384221781850058304

def SurrogateDiagonalTailChunk001Sub001Block048Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26698
    = surrogateDiagTailX0RatChunk001Sub001Block048Part000

theorem surrogateDiagonalTailChunk001Sub001Block048Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part000] using hcert

def TailChunk001Sub001Block048Part001SupportExplicit : Finset ℕ :=
  ([26699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26699
    = surrogateDiagTailX0RatChunk001Sub001Block048Part001

theorem surrogateDiagonalTailChunk001Sub001Block048Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part001] using hcert

def TailChunk001Sub001Block048Part002SupportExplicit : Finset ℕ :=
  ([26701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26701
    = surrogateDiagTailX0RatChunk001Sub001Block048Part002

theorem surrogateDiagonalTailChunk001Sub001Block048Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part002] using hcert

def TailChunk001Sub001Block048Part003SupportExplicit : Finset ℕ :=
  ([26706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part003 : ℚ :=
  (990625061 : ℚ) / 12550957889640000

def SurrogateDiagonalTailChunk001Sub001Block048Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26706
    = surrogateDiagTailX0RatChunk001Sub001Block048Part003

theorem surrogateDiagonalTailChunk001Sub001Block048Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part003] using hcert

def TailChunk001Sub001Block048Part004SupportExplicit : Finset ℕ :=
  ([26707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part004 : ℚ :=
  (1556609607 : ℚ) / 3318823407016345600

def SurrogateDiagonalTailChunk001Sub001Block048Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26707
    = surrogateDiagTailX0RatChunk001Sub001Block048Part004

theorem surrogateDiagonalTailChunk001Sub001Block048Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part004] using hcert

def TailChunk001Sub001Block048Part005SupportExplicit : Finset ℕ :=
  ([26709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part005 : ℚ :=
  (2576476925 : ℚ) / 2566760733339328512

def SurrogateDiagonalTailChunk001Sub001Block048Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26709
    = surrogateDiagTailX0RatChunk001Sub001Block048Part005

theorem surrogateDiagonalTailChunk001Sub001Block048Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part005] using hcert

def TailChunk001Sub001Block048Part006SupportExplicit : Finset ℕ :=
  ([26710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part006 : ℚ :=
  (11895794683 : ℚ) / 433761104665958400

def SurrogateDiagonalTailChunk001Sub001Block048Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26710
    = surrogateDiagTailX0RatChunk001Sub001Block048Part006

theorem surrogateDiagonalTailChunk001Sub001Block048Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part006] using hcert

def TailChunk001Sub001Block048Part007SupportExplicit : Finset ℕ :=
  ([26711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26711
    = surrogateDiagTailX0RatChunk001Sub001Block048Part007

theorem surrogateDiagonalTailChunk001Sub001Block048Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part007] using hcert

def TailChunk001Sub001Block048Part008SupportExplicit : Finset ℕ :=
  ([26713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26713
    = surrogateDiagTailX0RatChunk001Sub001Block048Part008

theorem surrogateDiagonalTailChunk001Sub001Block048Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part008] using hcert

def TailChunk001Sub001Block048Part009SupportExplicit : Finset ℕ :=
  ([26715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part009 : ℚ :=
  (674461270025 : ℚ) / 36327660386594586624

def SurrogateDiagonalTailChunk001Sub001Block048Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26715
    = surrogateDiagTailX0RatChunk001Sub001Block048Part009

theorem surrogateDiagonalTailChunk001Sub001Block048Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part009] using hcert

def TailChunk001Sub001Block048Part010SupportExplicit : Finset ℕ :=
  ([26717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part010 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26717
    = surrogateDiagTailX0RatChunk001Sub001Block048Part010

theorem surrogateDiagonalTailChunk001Sub001Block048Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part010] using hcert

def TailChunk001Sub001Block048Part011SupportExplicit : Finset ℕ :=
  ([26718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part011 : ℚ :=
  (49862903131 : ℚ) / 557367729271603200

def SurrogateDiagonalTailChunk001Sub001Block048Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26718
    = surrogateDiagTailX0RatChunk001Sub001Block048Part011

theorem surrogateDiagonalTailChunk001Sub001Block048Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part011] using hcert

def TailChunk001Sub001Block048Part012SupportExplicit : Finset ℕ :=
  ([26719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part012 : ℚ :=
  (3164427139 : ℚ) / 688069777926297600

def SurrogateDiagonalTailChunk001Sub001Block048Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26719
    = surrogateDiagTailX0RatChunk001Sub001Block048Part012

theorem surrogateDiagonalTailChunk001Sub001Block048Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part012] using hcert

def TailChunk001Sub001Block048Part013SupportExplicit : Finset ℕ :=
  ([26722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part013 : ℚ :=
  (908162189 : ℚ) / 461630442627000000

def SurrogateDiagonalTailChunk001Sub001Block048Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26722
    = surrogateDiagTailX0RatChunk001Sub001Block048Part013

theorem surrogateDiagonalTailChunk001Sub001Block048Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part013] using hcert

def TailChunk001Sub001Block048Part014SupportExplicit : Finset ℕ :=
  ([26723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part014 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26723
    = surrogateDiagTailX0RatChunk001Sub001Block048Part014

theorem surrogateDiagonalTailChunk001Sub001Block048Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part014] using hcert

def TailChunk001Sub001Block048Part015SupportExplicit : Finset ℕ :=
  ([26726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part015 : ℚ :=
  (22425422975 : ℚ) / 953400757118059008

def SurrogateDiagonalTailChunk001Sub001Block048Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26726
    = surrogateDiagTailX0RatChunk001Sub001Block048Part015

theorem surrogateDiagonalTailChunk001Sub001Block048Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part015] using hcert

def TailChunk001Sub001Block048Part016SupportExplicit : Finset ℕ :=
  ([26727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part016 : ℚ :=
  (1296114931 : ℚ) / 2292048758088000000

def SurrogateDiagonalTailChunk001Sub001Block048Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26727
    = surrogateDiagTailX0RatChunk001Sub001Block048Part016

theorem surrogateDiagonalTailChunk001Sub001Block048Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part016] using hcert

def TailChunk001Sub001Block048Part017SupportExplicit : Finset ℕ :=
  ([26729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part017 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26729
    = surrogateDiagTailX0RatChunk001Sub001Block048Part017

theorem surrogateDiagonalTailChunk001Sub001Block048Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part017] using hcert

def TailChunk001Sub001Block048Part018SupportExplicit : Finset ℕ :=
  ([26731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26731
    = surrogateDiagTailX0RatChunk001Sub001Block048Part018

theorem surrogateDiagonalTailChunk001Sub001Block048Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part018] using hcert

def TailChunk001Sub001Block048Part019SupportExplicit : Finset ℕ :=
  ([26733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part019 : ℚ :=
  (1167152260225 : ℚ) / 103280327322735771648

def SurrogateDiagonalTailChunk001Sub001Block048Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26733
    = surrogateDiagTailX0RatChunk001Sub001Block048Part019

theorem surrogateDiagonalTailChunk001Sub001Block048Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part019] using hcert

def TailChunk001Sub001Block048Part020SupportExplicit : Finset ℕ :=
  ([26734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26734
    = surrogateDiagTailX0RatChunk001Sub001Block048Part020

theorem surrogateDiagonalTailChunk001Sub001Block048Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part020] using hcert

def TailChunk001Sub001Block048Part021SupportExplicit : Finset ℕ :=
  ([26735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part021 : ℚ :=
  (1787482769125 : ℚ) / 522856657071349843968

def SurrogateDiagonalTailChunk001Sub001Block048Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26735
    = surrogateDiagTailX0RatChunk001Sub001Block048Part021

theorem surrogateDiagonalTailChunk001Sub001Block048Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part021] using hcert

def TailChunk001Sub001Block048Part022SupportExplicit : Finset ℕ :=
  ([26737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block048Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26737
    = surrogateDiagTailX0RatChunk001Sub001Block048Part022

theorem surrogateDiagonalTailChunk001Sub001Block048Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part022] using hcert

def TailChunk001Sub001Block048Part023SupportExplicit : Finset ℕ :=
  ([26738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part023 : ℚ :=
  (2052202317 : ℚ) / 917548538058342400

def SurrogateDiagonalTailChunk001Sub001Block048Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26738
    = surrogateDiagTailX0RatChunk001Sub001Block048Part023

theorem surrogateDiagonalTailChunk001Sub001Block048Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part023] using hcert

def TailChunk001Sub001Block048Part024SupportExplicit : Finset ℕ :=
  ([26742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block048Part024 : ℚ :=
  (310405269025 : ℚ) / 3943370460749832192

def SurrogateDiagonalTailChunk001Sub001Block048Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26742
    = surrogateDiagTailX0RatChunk001Sub001Block048Part024

theorem surrogateDiagonalTailChunk001Sub001Block048Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block048Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block048Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block048Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block048Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block048Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block048HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block048Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block048Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block048Part000
    + surrogateDiagTailX0RatChunk001Sub001Block048Part001
    + surrogateDiagTailX0RatChunk001Sub001Block048Part002
    + surrogateDiagTailX0RatChunk001Sub001Block048Part003
    + surrogateDiagTailX0RatChunk001Sub001Block048Part004
    + surrogateDiagTailX0RatChunk001Sub001Block048Part005
    + surrogateDiagTailX0RatChunk001Sub001Block048Part006
    + surrogateDiagTailX0RatChunk001Sub001Block048Part007
    + surrogateDiagTailX0RatChunk001Sub001Block048Part008
    + surrogateDiagTailX0RatChunk001Sub001Block048Part009

def surrogateDiagonalTailChunk001Sub001Block048MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block048Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block048Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block048Part010
    + surrogateDiagTailX0RatChunk001Sub001Block048Part011
    + surrogateDiagTailX0RatChunk001Sub001Block048Part012
    + surrogateDiagTailX0RatChunk001Sub001Block048Part013
    + surrogateDiagTailX0RatChunk001Sub001Block048Part014
    + surrogateDiagTailX0RatChunk001Sub001Block048Part015
    + surrogateDiagTailX0RatChunk001Sub001Block048Part016
    + surrogateDiagTailX0RatChunk001Sub001Block048Part017
    + surrogateDiagTailX0RatChunk001Sub001Block048Part018
    + surrogateDiagTailX0RatChunk001Sub001Block048Part019

def surrogateDiagonalTailChunk001Sub001Block048TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block048Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block048Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block048Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block048Part020
    + surrogateDiagTailX0RatChunk001Sub001Block048Part021
    + surrogateDiagTailX0RatChunk001Sub001Block048Part022
    + surrogateDiagTailX0RatChunk001Sub001Block048Part023
    + surrogateDiagTailX0RatChunk001Sub001Block048Part024

def surrogateDiagonalTailChunk001Sub001Block048Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block048HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block048MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block048TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block048 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block048Part000
    + surrogateDiagTailX0RatChunk001Sub001Block048Part001
    + surrogateDiagTailX0RatChunk001Sub001Block048Part002
    + surrogateDiagTailX0RatChunk001Sub001Block048Part003
    + surrogateDiagTailX0RatChunk001Sub001Block048Part004
    + surrogateDiagTailX0RatChunk001Sub001Block048Part005
    + surrogateDiagTailX0RatChunk001Sub001Block048Part006
    + surrogateDiagTailX0RatChunk001Sub001Block048Part007
    + surrogateDiagTailX0RatChunk001Sub001Block048Part008
    + surrogateDiagTailX0RatChunk001Sub001Block048Part009
    + surrogateDiagTailX0RatChunk001Sub001Block048Part010
    + surrogateDiagTailX0RatChunk001Sub001Block048Part011
    + surrogateDiagTailX0RatChunk001Sub001Block048Part012
    + surrogateDiagTailX0RatChunk001Sub001Block048Part013
    + surrogateDiagTailX0RatChunk001Sub001Block048Part014
    + surrogateDiagTailX0RatChunk001Sub001Block048Part015
    + surrogateDiagTailX0RatChunk001Sub001Block048Part016
    + surrogateDiagTailX0RatChunk001Sub001Block048Part017
    + surrogateDiagTailX0RatChunk001Sub001Block048Part018
    + surrogateDiagTailX0RatChunk001Sub001Block048Part019
    + surrogateDiagTailX0RatChunk001Sub001Block048Part020
    + surrogateDiagTailX0RatChunk001Sub001Block048Part021
    + surrogateDiagTailX0RatChunk001Sub001Block048Part022
    + surrogateDiagTailX0RatChunk001Sub001Block048Part023
    + surrogateDiagTailX0RatChunk001Sub001Block048Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block048_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block048Head + surrogateDiagTailX0RatChunk001Sub001Block048Mid + surrogateDiagTailX0RatChunk001Sub001Block048Tail =
      surrogateDiagTailX0RatChunk001Sub001Block048 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block048Head surrogateDiagTailX0RatChunk001Sub001Block048Mid surrogateDiagTailX0RatChunk001Sub001Block048Tail surrogateDiagTailX0RatChunk001Sub001Block048
  ring

def SurrogateDiagonalTailChunk001Sub001Block048HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block048HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block048Head

def SurrogateDiagonalTailChunk001Sub001Block048MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block048MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block048Mid

def SurrogateDiagonalTailChunk001Sub001Block048TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block048TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block048Tail

theorem surrogateDiagonalTailChunk001Sub001Block048_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block048HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block048MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block048TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block048Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block048 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block048HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block048MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block048TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block048Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block048_eq_head_add_mid_add_tail

/-- Block 049 covers tail-support indices [16225,16250) and q from 26743 to 26782. -/

def TailChunk001Sub001Block049Part000SupportExplicit : Finset ℕ :=
  ([26743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part000 : ℚ :=
  (195513654925 : ℚ) / 1165336980482546761728

def SurrogateDiagonalTailChunk001Sub001Block049Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26743
    = surrogateDiagTailX0RatChunk001Sub001Block049Part000

theorem surrogateDiagonalTailChunk001Sub001Block049Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part000CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part000CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part000SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part000] using hcert

def TailChunk001Sub001Block049Part001SupportExplicit : Finset ℕ :=
  ([26745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part001 : ℚ :=
  (149194989125 : ℚ) / 12910040915341971456

def SurrogateDiagonalTailChunk001Sub001Block049Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26745
    = surrogateDiagTailX0RatChunk001Sub001Block049Part001

theorem surrogateDiagonalTailChunk001Sub001Block049Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part001CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part001CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part001SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part001] using hcert

def TailChunk001Sub001Block049Part002SupportExplicit : Finset ℕ :=
  ([26746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part002 : ℚ :=
  (436048441 : ℚ) / 287429134493632320

def SurrogateDiagonalTailChunk001Sub001Block049Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26746
    = surrogateDiagTailX0RatChunk001Sub001Block049Part002

theorem surrogateDiagonalTailChunk001Sub001Block049Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part002CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part002CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part002SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part002] using hcert

def TailChunk001Sub001Block049Part003SupportExplicit : Finset ℕ :=
  ([26747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part003 : ℚ :=
  (36511201367 : ℚ) / 13801151005113369600

def SurrogateDiagonalTailChunk001Sub001Block049Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26747
    = surrogateDiagTailX0RatChunk001Sub001Block049Part003

theorem surrogateDiagonalTailChunk001Sub001Block049Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part003CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part003CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part003SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part003] using hcert

def TailChunk001Sub001Block049Part004SupportExplicit : Finset ℕ :=
  ([26749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part004 : ℚ :=
  (142826241675 : ℚ) / 355976099149854257536

def SurrogateDiagonalTailChunk001Sub001Block049Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26749
    = surrogateDiagTailX0RatChunk001Sub001Block049Part004

theorem surrogateDiagonalTailChunk001Sub001Block049Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part004CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part004CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part004SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part004] using hcert

def TailChunk001Sub001Block049Part005SupportExplicit : Finset ℕ :=
  ([26751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part005 : ℚ :=
  (92627 : ℚ) / 118881339310080

def SurrogateDiagonalTailChunk001Sub001Block049Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26751
    = surrogateDiagTailX0RatChunk001Sub001Block049Part005

theorem surrogateDiagonalTailChunk001Sub001Block049Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part005CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part005CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part005SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part005] using hcert

def TailChunk001Sub001Block049Part006SupportExplicit : Finset ℕ :=
  ([26753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part006 : ℚ :=
  (11508944887 : ℚ) / 44730209513868163200

def SurrogateDiagonalTailChunk001Sub001Block049Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26753
    = surrogateDiagTailX0RatChunk001Sub001Block049Part006

theorem surrogateDiagonalTailChunk001Sub001Block049Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part006CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part006CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part006SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part006] using hcert

def TailChunk001Sub001Block049Part007SupportExplicit : Finset ℕ :=
  ([26755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part007 : ℚ :=
  (4773751383 : ℚ) / 1398462047148800000

def SurrogateDiagonalTailChunk001Sub001Block049Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26755
    = surrogateDiagTailX0RatChunk001Sub001Block049Part007

theorem surrogateDiagonalTailChunk001Sub001Block049Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part007CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part007CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part007SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part007] using hcert

def TailChunk001Sub001Block049Part008SupportExplicit : Finset ℕ :=
  ([26758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part008 : ℚ :=
  (13135571375 : ℚ) / 3474757240563695616

def SurrogateDiagonalTailChunk001Sub001Block049Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26758
    = surrogateDiagTailX0RatChunk001Sub001Block049Part008

theorem surrogateDiagonalTailChunk001Sub001Block049Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part008CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part008CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part008SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part008] using hcert

def TailChunk001Sub001Block049Part009SupportExplicit : Finset ℕ :=
  ([26759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block049Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26759
    = surrogateDiagTailX0RatChunk001Sub001Block049Part009

theorem surrogateDiagonalTailChunk001Sub001Block049Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part009CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part009CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part009SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part009] using hcert

def TailChunk001Sub001Block049Part010SupportExplicit : Finset ℕ :=
  ([26761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part010 : ℚ :=
  (913735093175 : ℚ) / 345751916142964129344

def SurrogateDiagonalTailChunk001Sub001Block049Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26761
    = surrogateDiagTailX0RatChunk001Sub001Block049Part010

theorem surrogateDiagonalTailChunk001Sub001Block049Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part010CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part010CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part010SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part010] using hcert

def TailChunk001Sub001Block049Part011SupportExplicit : Finset ℕ :=
  ([26762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block049Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26762
    = surrogateDiagTailX0RatChunk001Sub001Block049Part011

theorem surrogateDiagonalTailChunk001Sub001Block049Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part011CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part011CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part011SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part011] using hcert

def TailChunk001Sub001Block049Part012SupportExplicit : Finset ℕ :=
  ([26763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part012 : ℚ :=
  (19937434129 : ℚ) / 6888852855072000000

def SurrogateDiagonalTailChunk001Sub001Block049Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26763
    = surrogateDiagTailX0RatChunk001Sub001Block049Part012

theorem surrogateDiagonalTailChunk001Sub001Block049Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part012CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part012CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part012SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part012] using hcert

def TailChunk001Sub001Block049Part013SupportExplicit : Finset ℕ :=
  ([26765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part013 : ℚ :=
  (12531060621 : ℚ) / 3120246751232000000

def SurrogateDiagonalTailChunk001Sub001Block049Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26765
    = surrogateDiagTailX0RatChunk001Sub001Block049Part013

theorem surrogateDiagonalTailChunk001Sub001Block049Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part013CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part013CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part013SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part013] using hcert

def TailChunk001Sub001Block049Part014SupportExplicit : Finset ℕ :=
  ([26767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part014 : ℚ :=
  (7374599053 : ℚ) / 5101347042931507200

def SurrogateDiagonalTailChunk001Sub001Block049Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26767
    = surrogateDiagTailX0RatChunk001Sub001Block049Part014

theorem surrogateDiagonalTailChunk001Sub001Block049Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part014CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part014CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part014SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part014] using hcert

def TailChunk001Sub001Block049Part015SupportExplicit : Finset ℕ :=
  ([26769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part015 : ℚ :=
  (41675 : ℚ) / 16897311405714816

def SurrogateDiagonalTailChunk001Sub001Block049Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26769
    = surrogateDiagTailX0RatChunk001Sub001Block049Part015

theorem surrogateDiagonalTailChunk001Sub001Block049Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part015CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part015CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part015SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part015] using hcert

def TailChunk001Sub001Block049Part016SupportExplicit : Finset ℕ :=
  ([26770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part016 : ℚ :=
  (298731099175 : ℚ) / 10941831080113176576

def SurrogateDiagonalTailChunk001Sub001Block049Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26770
    = surrogateDiagTailX0RatChunk001Sub001Block049Part016

theorem surrogateDiagonalTailChunk001Sub001Block049Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part016CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part016CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part016SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part016] using hcert

def TailChunk001Sub001Block049Part017SupportExplicit : Finset ℕ :=
  ([26771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part017 : ℚ :=
  (500941379725 : ℚ) / 1031638398326903144448

def SurrogateDiagonalTailChunk001Sub001Block049Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26771
    = surrogateDiagTailX0RatChunk001Sub001Block049Part017

theorem surrogateDiagonalTailChunk001Sub001Block049Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part017CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part017CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part017SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part017] using hcert

def TailChunk001Sub001Block049Part018SupportExplicit : Finset ℕ :=
  ([26773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part018 : ℚ :=
  (8990407639 : ℚ) / 46271885695529779200

def SurrogateDiagonalTailChunk001Sub001Block049Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26773
    = surrogateDiagTailX0RatChunk001Sub001Block049Part018

theorem surrogateDiagonalTailChunk001Sub001Block049Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part018CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part018CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part018SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part018] using hcert

def TailChunk001Sub001Block049Part019SupportExplicit : Finset ℕ :=
  ([26774] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part019 : ℚ :=
  (4967593047 : ℚ) / 728953617016422400

def SurrogateDiagonalTailChunk001Sub001Block049Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26774
    = surrogateDiagTailX0RatChunk001Sub001Block049Part019

theorem surrogateDiagonalTailChunk001Sub001Block049Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part019CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part019CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part019SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part019] using hcert

def TailChunk001Sub001Block049Part020SupportExplicit : Finset ℕ :=
  ([26777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk001Sub001Block049Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26777
    = surrogateDiagTailX0RatChunk001Sub001Block049Part020

theorem surrogateDiagonalTailChunk001Sub001Block049Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part020CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part020CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part020SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part020] using hcert

def TailChunk001Sub001Block049Part021SupportExplicit : Finset ℕ :=
  ([26778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part021 : ℚ :=
  (622482662975 : ℚ) / 7929304751624276544

def SurrogateDiagonalTailChunk001Sub001Block049Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26778
    = surrogateDiagTailX0RatChunk001Sub001Block049Part021

theorem surrogateDiagonalTailChunk001Sub001Block049Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part021CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part021CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part021SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part021] using hcert

def TailChunk001Sub001Block049Part022SupportExplicit : Finset ℕ :=
  ([26779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part022 : ℚ :=
  (6493007437 : ℚ) / 47707679583447091200

def SurrogateDiagonalTailChunk001Sub001Block049Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26779
    = surrogateDiagTailX0RatChunk001Sub001Block049Part022

theorem surrogateDiagonalTailChunk001Sub001Block049Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part022CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part022CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part022SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part022] using hcert

def TailChunk001Sub001Block049Part023SupportExplicit : Finset ℕ :=
  ([26781] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part023 : ℚ :=
  (1134125 : ℚ) / 2218815513427968

def SurrogateDiagonalTailChunk001Sub001Block049Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26781
    = surrogateDiagTailX0RatChunk001Sub001Block049Part023

theorem surrogateDiagonalTailChunk001Sub001Block049Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part023CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part023CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part023SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part023] using hcert

def TailChunk001Sub001Block049Part024SupportExplicit : Finset ℕ :=
  ([26782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk001Sub001Block049Part024 : ℚ :=
  (229375694675 : ℚ) / 21654762079927025664

def SurrogateDiagonalTailChunk001Sub001Block049Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 26782
    = surrogateDiagTailX0RatChunk001Sub001Block049Part024

theorem surrogateDiagonalTailChunk001Sub001Block049Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk001Sub001Block049Part024CertificateAtX0 →
    (∑ q ∈ TailChunk001Sub001Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk001Sub001Block049Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk001Sub001Block049Part024CertificateAtX0 at hcert
  simpa [TailChunk001Sub001Block049Part024SupportExplicit, surrogateDiagTailX0RatChunk001Sub001Block049Part024] using hcert

def surrogateDiagonalTailChunk001Sub001Block049HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block049Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block049Head : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block049Part000
    + surrogateDiagTailX0RatChunk001Sub001Block049Part001
    + surrogateDiagTailX0RatChunk001Sub001Block049Part002
    + surrogateDiagTailX0RatChunk001Sub001Block049Part003
    + surrogateDiagTailX0RatChunk001Sub001Block049Part004
    + surrogateDiagTailX0RatChunk001Sub001Block049Part005
    + surrogateDiagTailX0RatChunk001Sub001Block049Part006
    + surrogateDiagTailX0RatChunk001Sub001Block049Part007
    + surrogateDiagTailX0RatChunk001Sub001Block049Part008
    + surrogateDiagTailX0RatChunk001Sub001Block049Part009

def surrogateDiagonalTailChunk001Sub001Block049MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block049Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block049Mid : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block049Part010
    + surrogateDiagTailX0RatChunk001Sub001Block049Part011
    + surrogateDiagTailX0RatChunk001Sub001Block049Part012
    + surrogateDiagTailX0RatChunk001Sub001Block049Part013
    + surrogateDiagTailX0RatChunk001Sub001Block049Part014
    + surrogateDiagTailX0RatChunk001Sub001Block049Part015
    + surrogateDiagTailX0RatChunk001Sub001Block049Part016
    + surrogateDiagTailX0RatChunk001Sub001Block049Part017
    + surrogateDiagTailX0RatChunk001Sub001Block049Part018
    + surrogateDiagTailX0RatChunk001Sub001Block049Part019

def surrogateDiagonalTailChunk001Sub001Block049TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk001Sub001Block049Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk001Sub001Block049Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk001Sub001Block049Tail : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block049Part020
    + surrogateDiagTailX0RatChunk001Sub001Block049Part021
    + surrogateDiagTailX0RatChunk001Sub001Block049Part022
    + surrogateDiagTailX0RatChunk001Sub001Block049Part023
    + surrogateDiagTailX0RatChunk001Sub001Block049Part024

def surrogateDiagonalTailChunk001Sub001Block049Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk001Sub001Block049HeadSum X0
    + surrogateDiagonalTailChunk001Sub001Block049MidSum X0
    + surrogateDiagonalTailChunk001Sub001Block049TailSum X0

def surrogateDiagTailX0RatChunk001Sub001Block049 : ℚ :=
  surrogateDiagTailX0RatChunk001Sub001Block049Part000
    + surrogateDiagTailX0RatChunk001Sub001Block049Part001
    + surrogateDiagTailX0RatChunk001Sub001Block049Part002
    + surrogateDiagTailX0RatChunk001Sub001Block049Part003
    + surrogateDiagTailX0RatChunk001Sub001Block049Part004
    + surrogateDiagTailX0RatChunk001Sub001Block049Part005
    + surrogateDiagTailX0RatChunk001Sub001Block049Part006
    + surrogateDiagTailX0RatChunk001Sub001Block049Part007
    + surrogateDiagTailX0RatChunk001Sub001Block049Part008
    + surrogateDiagTailX0RatChunk001Sub001Block049Part009
    + surrogateDiagTailX0RatChunk001Sub001Block049Part010
    + surrogateDiagTailX0RatChunk001Sub001Block049Part011
    + surrogateDiagTailX0RatChunk001Sub001Block049Part012
    + surrogateDiagTailX0RatChunk001Sub001Block049Part013
    + surrogateDiagTailX0RatChunk001Sub001Block049Part014
    + surrogateDiagTailX0RatChunk001Sub001Block049Part015
    + surrogateDiagTailX0RatChunk001Sub001Block049Part016
    + surrogateDiagTailX0RatChunk001Sub001Block049Part017
    + surrogateDiagTailX0RatChunk001Sub001Block049Part018
    + surrogateDiagTailX0RatChunk001Sub001Block049Part019
    + surrogateDiagTailX0RatChunk001Sub001Block049Part020
    + surrogateDiagTailX0RatChunk001Sub001Block049Part021
    + surrogateDiagTailX0RatChunk001Sub001Block049Part022
    + surrogateDiagTailX0RatChunk001Sub001Block049Part023
    + surrogateDiagTailX0RatChunk001Sub001Block049Part024

theorem surrogateDiagTailX0RatChunk001Sub001Block049_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk001Sub001Block049Head + surrogateDiagTailX0RatChunk001Sub001Block049Mid + surrogateDiagTailX0RatChunk001Sub001Block049Tail =
      surrogateDiagTailX0RatChunk001Sub001Block049 := by
  unfold surrogateDiagTailX0RatChunk001Sub001Block049Head surrogateDiagTailX0RatChunk001Sub001Block049Mid surrogateDiagTailX0RatChunk001Sub001Block049Tail surrogateDiagTailX0RatChunk001Sub001Block049
  ring

def SurrogateDiagonalTailChunk001Sub001Block049HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block049HeadSum X0 = surrogateDiagTailX0RatChunk001Sub001Block049Head

def SurrogateDiagonalTailChunk001Sub001Block049MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block049MidSum X0 = surrogateDiagTailX0RatChunk001Sub001Block049Mid

def SurrogateDiagonalTailChunk001Sub001Block049TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk001Sub001Block049TailSum X0 = surrogateDiagTailX0RatChunk001Sub001Block049Tail

theorem surrogateDiagonalTailChunk001Sub001Block049_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk001Sub001Block049HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk001Sub001Block049MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk001Sub001Block049TailCertificateAt X0) :
    surrogateDiagonalTailChunk001Sub001Block049Sum X0 = surrogateDiagTailX0RatChunk001Sub001Block049 := by
  unfold SurrogateDiagonalTailChunk001Sub001Block049HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk001Sub001Block049MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk001Sub001Block049TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk001Sub001Block049Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk001Sub001Block049_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
