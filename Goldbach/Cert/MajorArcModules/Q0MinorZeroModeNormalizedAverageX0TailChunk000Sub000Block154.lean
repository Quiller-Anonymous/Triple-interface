import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [154,155). -/

/- Block 154 covers tail-support indices [3850,3875) and q from 6385 to 6427. -/

def TailChunk000Sub000Block154Part000SupportExplicit : Finset ℕ :=
  ([6385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part000 : ℚ :=
  (967537748825 : ℚ) / 848475929085886464

def SurrogateDiagonalTailChunk000Sub000Block154Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6385
    = surrogateDiagTailX0RatChunk000Sub000Block154Part000

theorem surrogateDiagonalTailChunk000Sub000Block154Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part000] using hcert

def TailChunk000Sub000Block154Part001SupportExplicit : Finset ℕ :=
  ([6386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part001 : ℚ :=
  (1792326581 : ℚ) / 324794593929600

def SurrogateDiagonalTailChunk000Sub000Block154Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6386
    = surrogateDiagTailX0RatChunk000Sub000Block154Part001

theorem surrogateDiagonalTailChunk000Sub000Block154Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part001] using hcert

def TailChunk000Sub000Block154Part002SupportExplicit : Finset ℕ :=
  ([6387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part002 : ℚ :=
  (3466875 : ℚ) / 1673980542976

def SurrogateDiagonalTailChunk000Sub000Block154Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6387
    = surrogateDiagTailX0RatChunk000Sub000Block154Part002

theorem surrogateDiagonalTailChunk000Sub000Block154Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part002] using hcert

def TailChunk000Sub000Block154Part003SupportExplicit : Finset ℕ :=
  ([6389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part003 : ℚ :=
  (637801890625 : ℚ) / 1040941917519112992

def SurrogateDiagonalTailChunk000Sub000Block154Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6389
    = surrogateDiagTailX0RatChunk000Sub000Block154Part003

theorem surrogateDiagonalTailChunk000Sub000Block154Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part003] using hcert

def TailChunk000Sub000Block154Part004SupportExplicit : Finset ℕ :=
  ([6391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part004 : ℚ :=
  (75289944061 : ℚ) / 58606699092019200

def SurrogateDiagonalTailChunk000Sub000Block154Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6391
    = surrogateDiagTailX0RatChunk000Sub000Block154Part004

theorem surrogateDiagonalTailChunk000Sub000Block154Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part004] using hcert

def TailChunk000Sub000Block154Part005SupportExplicit : Finset ℕ :=
  ([6393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part005 : ℚ :=
  (11352479789 : ℚ) / 16470062641857600

def SurrogateDiagonalTailChunk000Sub000Block154Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6393
    = surrogateDiagTailX0RatChunk000Sub000Block154Part005

theorem surrogateDiagonalTailChunk000Sub000Block154Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part005] using hcert

def TailChunk000Sub000Block154Part006SupportExplicit : Finset ℕ :=
  ([6394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part006 : ℚ :=
  (1927947875 : ℚ) / 655675441826592

def SurrogateDiagonalTailChunk000Sub000Block154Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6394
    = surrogateDiagTailX0RatChunk000Sub000Block154Part006

theorem surrogateDiagonalTailChunk000Sub000Block154Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part006] using hcert

def TailChunk000Sub000Block154Part007SupportExplicit : Finset ℕ :=
  ([6395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part007 : ℚ :=
  (204662992175 : ℚ) / 853808047353897984

def SurrogateDiagonalTailChunk000Sub000Block154Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6395
    = surrogateDiagTailX0RatChunk000Sub000Block154Part007

theorem surrogateDiagonalTailChunk000Sub000Block154Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part007] using hcert

def TailChunk000Sub000Block154Part008SupportExplicit : Finset ℕ :=
  ([6397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block154Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6397
    = surrogateDiagTailX0RatChunk000Sub000Block154Part008

theorem surrogateDiagonalTailChunk000Sub000Block154Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part008] using hcert

def TailChunk000Sub000Block154Part009SupportExplicit : Finset ℕ :=
  ([6398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part009 : ℚ :=
  (9371341675 : ℚ) / 2189330145833472

def SurrogateDiagonalTailChunk000Sub000Block154Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6398
    = surrogateDiagTailX0RatChunk000Sub000Block154Part009

theorem surrogateDiagonalTailChunk000Sub000Block154Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part009] using hcert

def TailChunk000Sub000Block154Part010SupportExplicit : Finset ℕ :=
  ([6401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part010 : ℚ :=
  (32278703825 : ℚ) / 1837894820796186624

def SurrogateDiagonalTailChunk000Sub000Block154Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6401
    = surrogateDiagTailX0RatChunk000Sub000Block154Part010

theorem surrogateDiagonalTailChunk000Sub000Block154Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part010] using hcert

def TailChunk000Sub000Block154Part011SupportExplicit : Finset ℕ :=
  ([6402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part011 : ℚ :=
  (1304444791 : ℚ) / 84951642931200

def SurrogateDiagonalTailChunk000Sub000Block154Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6402
    = surrogateDiagTailX0RatChunk000Sub000Block154Part011

theorem surrogateDiagonalTailChunk000Sub000Block154Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part011] using hcert

def TailChunk000Sub000Block154Part012SupportExplicit : Finset ℕ :=
  ([6403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part012 : ℚ :=
  (111164322175 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub000Block154Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6403
    = surrogateDiagTailX0RatChunk000Sub000Block154Part012

theorem surrogateDiagonalTailChunk000Sub000Block154Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part012] using hcert

def TailChunk000Sub000Block154Part013SupportExplicit : Finset ℕ :=
  ([6405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part013 : ℚ :=
  (7751237483 : ℚ) / 2293694359142400

def SurrogateDiagonalTailChunk000Sub000Block154Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6405
    = surrogateDiagTailX0RatChunk000Sub000Block154Part013

theorem surrogateDiagonalTailChunk000Sub000Block154Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part013] using hcert

def TailChunk000Sub000Block154Part014SupportExplicit : Finset ℕ :=
  ([6406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part014 : ℚ :=
  (160300140625 : ℚ) / 65713133662742802

def SurrogateDiagonalTailChunk000Sub000Block154Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6406
    = surrogateDiagTailX0RatChunk000Sub000Block154Part014

theorem surrogateDiagonalTailChunk000Sub000Block154Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part014] using hcert

def TailChunk000Sub000Block154Part015SupportExplicit : Finset ℕ :=
  ([6407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part015 : ℚ :=
  (59435709475 : ℚ) / 3733110816584583168

def SurrogateDiagonalTailChunk000Sub000Block154Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6407
    = surrogateDiagTailX0RatChunk000Sub000Block154Part015

theorem surrogateDiagonalTailChunk000Sub000Block154Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part015] using hcert

def TailChunk000Sub000Block154Part016SupportExplicit : Finset ℕ :=
  ([6409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part016 : ℚ :=
  (142397092925 : ℚ) / 1044320740750393344

def SurrogateDiagonalTailChunk000Sub000Block154Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6409
    = surrogateDiagTailX0RatChunk000Sub000Block154Part016

theorem surrogateDiagonalTailChunk000Sub000Block154Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part016] using hcert

def TailChunk000Sub000Block154Part017SupportExplicit : Finset ℕ :=
  ([6410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part017 : ℚ :=
  (22581673699 : ℚ) / 4295826289459200

def SurrogateDiagonalTailChunk000Sub000Block154Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6410
    = surrogateDiagTailX0RatChunk000Sub000Block154Part017

theorem surrogateDiagonalTailChunk000Sub000Block154Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part017] using hcert

def TailChunk000Sub000Block154Part018SupportExplicit : Finset ℕ :=
  ([6411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part018 : ℚ :=
  (57052025 : ℚ) / 27755159666688

def SurrogateDiagonalTailChunk000Sub000Block154Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6411
    = surrogateDiagTailX0RatChunk000Sub000Block154Part018

theorem surrogateDiagonalTailChunk000Sub000Block154Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part018] using hcert

def TailChunk000Sub000Block154Part019SupportExplicit : Finset ℕ :=
  ([6414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part019 : ℚ :=
  (784946113675 : ℚ) / 52051332559915008

def SurrogateDiagonalTailChunk000Sub000Block154Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6414
    = surrogateDiagTailX0RatChunk000Sub000Block154Part019

theorem surrogateDiagonalTailChunk000Sub000Block154Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part019] using hcert

def TailChunk000Sub000Block154Part020SupportExplicit : Finset ℕ :=
  ([6415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part020 : ℚ :=
  (244163087675 : ℚ) / 216136909824297216

def SurrogateDiagonalTailChunk000Sub000Block154Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6415
    = surrogateDiagTailX0RatChunk000Sub000Block154Part020

theorem surrogateDiagonalTailChunk000Sub000Block154Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part020] using hcert

def TailChunk000Sub000Block154Part021SupportExplicit : Finset ℕ :=
  ([6418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part021 : ℚ :=
  (1286952682975 : ℚ) / 264828241851598848

def SurrogateDiagonalTailChunk000Sub000Block154Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6418
    = surrogateDiagTailX0RatChunk000Sub000Block154Part021

theorem surrogateDiagonalTailChunk000Sub000Block154Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part021] using hcert

def TailChunk000Sub000Block154Part022SupportExplicit : Finset ℕ :=
  ([6421] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part022 : ℚ :=
  (1030731025 : ℚ) / 1699131387285792

def SurrogateDiagonalTailChunk000Sub000Block154Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6421
    = surrogateDiagTailX0RatChunk000Sub000Block154Part022

theorem surrogateDiagonalTailChunk000Sub000Block154Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part022] using hcert

def TailChunk000Sub000Block154Part023SupportExplicit : Finset ℕ :=
  ([6423] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part023 : ℚ :=
  (28639577279 : ℚ) / 16781544565785600

def SurrogateDiagonalTailChunk000Sub000Block154Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6423
    = surrogateDiagTailX0RatChunk000Sub000Block154Part023

theorem surrogateDiagonalTailChunk000Sub000Block154Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part023] using hcert

def TailChunk000Sub000Block154Part024SupportExplicit : Finset ℕ :=
  ([6427] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block154Part024 : ℚ :=
  (645411390625 : ℚ) / 1065932618996630322

def SurrogateDiagonalTailChunk000Sub000Block154Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6427
    = surrogateDiagTailX0RatChunk000Sub000Block154Part024

theorem surrogateDiagonalTailChunk000Sub000Block154Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block154Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block154Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block154Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block154Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block154Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block154Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block154HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block154Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block154Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block154Part000
    + surrogateDiagTailX0RatChunk000Sub000Block154Part001
    + surrogateDiagTailX0RatChunk000Sub000Block154Part002
    + surrogateDiagTailX0RatChunk000Sub000Block154Part003
    + surrogateDiagTailX0RatChunk000Sub000Block154Part004
    + surrogateDiagTailX0RatChunk000Sub000Block154Part005
    + surrogateDiagTailX0RatChunk000Sub000Block154Part006
    + surrogateDiagTailX0RatChunk000Sub000Block154Part007
    + surrogateDiagTailX0RatChunk000Sub000Block154Part008
    + surrogateDiagTailX0RatChunk000Sub000Block154Part009

def surrogateDiagonalTailChunk000Sub000Block154MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block154Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block154Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block154Part010
    + surrogateDiagTailX0RatChunk000Sub000Block154Part011
    + surrogateDiagTailX0RatChunk000Sub000Block154Part012
    + surrogateDiagTailX0RatChunk000Sub000Block154Part013
    + surrogateDiagTailX0RatChunk000Sub000Block154Part014
    + surrogateDiagTailX0RatChunk000Sub000Block154Part015
    + surrogateDiagTailX0RatChunk000Sub000Block154Part016
    + surrogateDiagTailX0RatChunk000Sub000Block154Part017
    + surrogateDiagTailX0RatChunk000Sub000Block154Part018
    + surrogateDiagTailX0RatChunk000Sub000Block154Part019

def surrogateDiagonalTailChunk000Sub000Block154TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block154Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block154Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block154Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block154Part020
    + surrogateDiagTailX0RatChunk000Sub000Block154Part021
    + surrogateDiagTailX0RatChunk000Sub000Block154Part022
    + surrogateDiagTailX0RatChunk000Sub000Block154Part023
    + surrogateDiagTailX0RatChunk000Sub000Block154Part024

def surrogateDiagonalTailChunk000Sub000Block154Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block154HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block154MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block154TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block154 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block154Part000
    + surrogateDiagTailX0RatChunk000Sub000Block154Part001
    + surrogateDiagTailX0RatChunk000Sub000Block154Part002
    + surrogateDiagTailX0RatChunk000Sub000Block154Part003
    + surrogateDiagTailX0RatChunk000Sub000Block154Part004
    + surrogateDiagTailX0RatChunk000Sub000Block154Part005
    + surrogateDiagTailX0RatChunk000Sub000Block154Part006
    + surrogateDiagTailX0RatChunk000Sub000Block154Part007
    + surrogateDiagTailX0RatChunk000Sub000Block154Part008
    + surrogateDiagTailX0RatChunk000Sub000Block154Part009
    + surrogateDiagTailX0RatChunk000Sub000Block154Part010
    + surrogateDiagTailX0RatChunk000Sub000Block154Part011
    + surrogateDiagTailX0RatChunk000Sub000Block154Part012
    + surrogateDiagTailX0RatChunk000Sub000Block154Part013
    + surrogateDiagTailX0RatChunk000Sub000Block154Part014
    + surrogateDiagTailX0RatChunk000Sub000Block154Part015
    + surrogateDiagTailX0RatChunk000Sub000Block154Part016
    + surrogateDiagTailX0RatChunk000Sub000Block154Part017
    + surrogateDiagTailX0RatChunk000Sub000Block154Part018
    + surrogateDiagTailX0RatChunk000Sub000Block154Part019
    + surrogateDiagTailX0RatChunk000Sub000Block154Part020
    + surrogateDiagTailX0RatChunk000Sub000Block154Part021
    + surrogateDiagTailX0RatChunk000Sub000Block154Part022
    + surrogateDiagTailX0RatChunk000Sub000Block154Part023
    + surrogateDiagTailX0RatChunk000Sub000Block154Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block154_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block154Head + surrogateDiagTailX0RatChunk000Sub000Block154Mid + surrogateDiagTailX0RatChunk000Sub000Block154Tail =
      surrogateDiagTailX0RatChunk000Sub000Block154 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block154Head surrogateDiagTailX0RatChunk000Sub000Block154Mid surrogateDiagTailX0RatChunk000Sub000Block154Tail surrogateDiagTailX0RatChunk000Sub000Block154
  ring

def SurrogateDiagonalTailChunk000Sub000Block154HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block154HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block154Head

def SurrogateDiagonalTailChunk000Sub000Block154MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block154MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block154Mid

def SurrogateDiagonalTailChunk000Sub000Block154TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block154TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block154Tail

theorem surrogateDiagonalTailChunk000Sub000Block154_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block154HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block154MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block154TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block154Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block154 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block154HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block154MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block154TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block154Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block154_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
