import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [81,82). -/

/- Block 081 covers tail-support indices [2025,2050) and q from 3378 to 3415. -/

def TailChunk000Sub000Block081Part000SupportExplicit : Finset ℕ :=
  ([3378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part000 : ℚ :=
  (69256824775 : ℚ) / 997773838224672

def SurrogateDiagonalTailChunk000Sub000Block081Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3378
    = surrogateDiagTailX0RatChunk000Sub000Block081Part000

theorem surrogateDiagonalTailChunk000Sub000Block081Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part000] using hcert

def TailChunk000Sub000Block081Part001SupportExplicit : Finset ℕ :=
  ([3379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part001 : ℚ :=
  (27075034949 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub000Block081Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3379
    = surrogateDiagTailX0RatChunk000Sub000Block081Part001

theorem surrogateDiagonalTailChunk000Sub000Block081Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part001] using hcert

def TailChunk000Sub000Block081Part002SupportExplicit : Finset ℕ :=
  ([3382] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part002 : ℚ :=
  (251121089075 : ℚ) / 7870776354422784

def SurrogateDiagonalTailChunk000Sub000Block081Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3382
    = surrogateDiagTailX0RatChunk000Sub000Block081Part002

theorem surrogateDiagonalTailChunk000Sub000Block081Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part002] using hcert

def TailChunk000Sub000Block081Part003SupportExplicit : Finset ℕ :=
  ([3383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part003 : ℚ :=
  (219345239875 : ℚ) / 41977473890254848

def SurrogateDiagonalTailChunk000Sub000Block081Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3383
    = surrogateDiagTailX0RatChunk000Sub000Block081Part003

theorem surrogateDiagonalTailChunk000Sub000Block081Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part003] using hcert

def TailChunk000Sub000Block081Part004SupportExplicit : Finset ℕ :=
  ([3385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part004 : ℚ :=
  (1058165929525 : ℚ) / 133676051192905728

def SurrogateDiagonalTailChunk000Sub000Block081Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3385
    = surrogateDiagTailX0RatChunk000Sub000Block081Part004

theorem surrogateDiagonalTailChunk000Sub000Block081Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part004] using hcert

def TailChunk000Sub000Block081Part005SupportExplicit : Finset ℕ :=
  ([3386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part005 : ℚ :=
  (59689635425 : ℚ) / 2277119300153472

def SurrogateDiagonalTailChunk000Sub000Block081Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3386
    = surrogateDiagTailX0RatChunk000Sub000Block081Part005

theorem surrogateDiagonalTailChunk000Sub000Block081Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part005] using hcert

def TailChunk000Sub000Block081Part006SupportExplicit : Finset ℕ :=
  ([3387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part006 : ℚ :=
  (875547582175 : ℚ) / 64771393426587648

def SurrogateDiagonalTailChunk000Sub000Block081Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3387
    = surrogateDiagTailX0RatChunk000Sub000Block081Part006

theorem surrogateDiagonalTailChunk000Sub000Block081Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part006] using hcert

def TailChunk000Sub000Block081Part007SupportExplicit : Finset ℕ :=
  ([3389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part007 : ℚ :=
  (1435377991975 : ℚ) / 329458309386019968

def SurrogateDiagonalTailChunk000Sub000Block081Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3389
    = surrogateDiagTailX0RatChunk000Sub000Block081Part007

theorem surrogateDiagonalTailChunk000Sub000Block081Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part007] using hcert

def TailChunk000Sub000Block081Part008SupportExplicit : Finset ℕ :=
  ([3390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part008 : ℚ :=
  (284774567275 : ℚ) / 1611606081404928

def SurrogateDiagonalTailChunk000Sub000Block081Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3390
    = surrogateDiagTailX0RatChunk000Sub000Block081Part008

theorem surrogateDiagonalTailChunk000Sub000Block081Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part008] using hcert

def TailChunk000Sub000Block081Part009SupportExplicit : Finset ℕ :=
  ([3391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part009 : ℚ :=
  (287472025 : ℚ) / 132094776082482

def SurrogateDiagonalTailChunk000Sub000Block081Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3391
    = surrogateDiagTailX0RatChunk000Sub000Block081Part009

theorem surrogateDiagonalTailChunk000Sub000Block081Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part009] using hcert

def TailChunk000Sub000Block081Part010SupportExplicit : Finset ℕ :=
  ([3394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part010 : ℚ :=
  (179916067275 : ℚ) / 6896186465714176

def SurrogateDiagonalTailChunk000Sub000Block081Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3394
    = surrogateDiagTailX0RatChunk000Sub000Block081Part010

theorem surrogateDiagonalTailChunk000Sub000Block081Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part010] using hcert

def TailChunk000Sub000Block081Part011SupportExplicit : Finset ℕ :=
  ([3395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part011 : ℚ :=
  (576036452275 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block081Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3395
    = surrogateDiagTailX0RatChunk000Sub000Block081Part011

theorem surrogateDiagonalTailChunk000Sub000Block081Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part011] using hcert

def TailChunk000Sub000Block081Part012SupportExplicit : Finset ℕ :=
  ([3397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part012 : ℚ :=
  (707535959125 : ℚ) / 288006594038287488

def SurrogateDiagonalTailChunk000Sub000Block081Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3397
    = surrogateDiagTailX0RatChunk000Sub000Block081Part012

theorem surrogateDiagonalTailChunk000Sub000Block081Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part012] using hcert

def TailChunk000Sub000Block081Part013SupportExplicit : Finset ℕ :=
  ([3398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part013 : ℚ :=
  (60113465825 : ℚ) / 2309591077410312

def SurrogateDiagonalTailChunk000Sub000Block081Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3398
    = surrogateDiagTailX0RatChunk000Sub000Block081Part013

theorem surrogateDiagonalTailChunk000Sub000Block081Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part013] using hcert

def TailChunk000Sub000Block081Part014SupportExplicit : Finset ℕ :=
  ([3399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part014 : ℚ :=
  (20773894711 : ℚ) / 1732237834291200

def SurrogateDiagonalTailChunk000Sub000Block081Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3399
    = surrogateDiagTailX0RatChunk000Sub000Block081Part014

theorem surrogateDiagonalTailChunk000Sub000Block081Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part014] using hcert

def TailChunk000Sub000Block081Part015SupportExplicit : Finset ℕ :=
  ([3401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part015 : ℚ :=
  (700775540425 : ℚ) / 263509871084569728

def SurrogateDiagonalTailChunk000Sub000Block081Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3401
    = surrogateDiagTailX0RatChunk000Sub000Block081Part015

theorem surrogateDiagonalTailChunk000Sub000Block081Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part015] using hcert

def TailChunk000Sub000Block081Part016SupportExplicit : Finset ℕ :=
  ([3403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part016 : ℚ :=
  (27634209497 : ℚ) / 5788315959705600

def SurrogateDiagonalTailChunk000Sub000Block081Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3403
    = surrogateDiagTailX0RatChunk000Sub000Block081Part016

theorem surrogateDiagonalTailChunk000Sub000Block081Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part016] using hcert

def TailChunk000Sub000Block081Part017SupportExplicit : Finset ℕ :=
  ([3405] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part017 : ℚ :=
  (309318733925 : ℚ) / 13359511181082624

def SurrogateDiagonalTailChunk000Sub000Block081Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3405
    = surrogateDiagTailX0RatChunk000Sub000Block081Part017

theorem surrogateDiagonalTailChunk000Sub000Block081Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part017] using hcert

def TailChunk000Sub000Block081Part018SupportExplicit : Finset ℕ :=
  ([3406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part018 : ℚ :=
  (994184519 : ℚ) / 29617967208960

def SurrogateDiagonalTailChunk000Sub000Block081Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3406
    = surrogateDiagTailX0RatChunk000Sub000Block081Part018

theorem surrogateDiagonalTailChunk000Sub000Block081Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part018] using hcert

def TailChunk000Sub000Block081Part019SupportExplicit : Finset ℕ :=
  ([3407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part019 : ℚ :=
  (1450665933775 : ℚ) / 336515779445189448

def SurrogateDiagonalTailChunk000Sub000Block081Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3407
    = surrogateDiagTailX0RatChunk000Sub000Block081Part019

theorem surrogateDiagonalTailChunk000Sub000Block081Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part019] using hcert

def TailChunk000Sub000Block081Part020SupportExplicit : Finset ℕ :=
  ([3409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part020 : ℚ :=
  (1183038427375 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub000Block081Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3409
    = surrogateDiagTailX0RatChunk000Sub000Block081Part020

theorem surrogateDiagonalTailChunk000Sub000Block081Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part020] using hcert

def TailChunk000Sub000Block081Part021SupportExplicit : Finset ℕ :=
  ([3410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part021 : ℚ :=
  (15105493579 : ℚ) / 207401472000000

def SurrogateDiagonalTailChunk000Sub000Block081Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3410
    = surrogateDiagTailX0RatChunk000Sub000Block081Part021

theorem surrogateDiagonalTailChunk000Sub000Block081Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part021] using hcert

def TailChunk000Sub000Block081Part022SupportExplicit : Finset ℕ :=
  ([3413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part022 : ℚ :=
  (182008890625 : ℚ) / 84723318376380192

def SurrogateDiagonalTailChunk000Sub000Block081Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3413
    = surrogateDiagTailX0RatChunk000Sub000Block081Part022

theorem surrogateDiagonalTailChunk000Sub000Block081Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part022] using hcert

def TailChunk000Sub000Block081Part023SupportExplicit : Finset ℕ :=
  ([3414] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part023 : ℚ :=
  (1136175 : ℚ) / 13010780672

def SurrogateDiagonalTailChunk000Sub000Block081Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3414
    = surrogateDiagTailX0RatChunk000Sub000Block081Part023

theorem surrogateDiagonalTailChunk000Sub000Block081Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part023] using hcert

def TailChunk000Sub000Block081Part024SupportExplicit : Finset ℕ :=
  ([3415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block081Part024 : ℚ :=
  (640899822775 : ℚ) / 138485506203568128

def SurrogateDiagonalTailChunk000Sub000Block081Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3415
    = surrogateDiagTailX0RatChunk000Sub000Block081Part024

theorem surrogateDiagonalTailChunk000Sub000Block081Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block081Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block081Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block081Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block081Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block081Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block081HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block081Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block081Part000
    + surrogateDiagTailX0RatChunk000Sub000Block081Part001
    + surrogateDiagTailX0RatChunk000Sub000Block081Part002
    + surrogateDiagTailX0RatChunk000Sub000Block081Part003
    + surrogateDiagTailX0RatChunk000Sub000Block081Part004
    + surrogateDiagTailX0RatChunk000Sub000Block081Part005
    + surrogateDiagTailX0RatChunk000Sub000Block081Part006
    + surrogateDiagTailX0RatChunk000Sub000Block081Part007
    + surrogateDiagTailX0RatChunk000Sub000Block081Part008
    + surrogateDiagTailX0RatChunk000Sub000Block081Part009

def surrogateDiagonalTailChunk000Sub000Block081MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block081Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block081Part010
    + surrogateDiagTailX0RatChunk000Sub000Block081Part011
    + surrogateDiagTailX0RatChunk000Sub000Block081Part012
    + surrogateDiagTailX0RatChunk000Sub000Block081Part013
    + surrogateDiagTailX0RatChunk000Sub000Block081Part014
    + surrogateDiagTailX0RatChunk000Sub000Block081Part015
    + surrogateDiagTailX0RatChunk000Sub000Block081Part016
    + surrogateDiagTailX0RatChunk000Sub000Block081Part017
    + surrogateDiagTailX0RatChunk000Sub000Block081Part018
    + surrogateDiagTailX0RatChunk000Sub000Block081Part019

def surrogateDiagonalTailChunk000Sub000Block081TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block081Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block081Part020
    + surrogateDiagTailX0RatChunk000Sub000Block081Part021
    + surrogateDiagTailX0RatChunk000Sub000Block081Part022
    + surrogateDiagTailX0RatChunk000Sub000Block081Part023
    + surrogateDiagTailX0RatChunk000Sub000Block081Part024

def surrogateDiagonalTailChunk000Sub000Block081Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block081HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block081MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block081TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block081 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block081Part000
    + surrogateDiagTailX0RatChunk000Sub000Block081Part001
    + surrogateDiagTailX0RatChunk000Sub000Block081Part002
    + surrogateDiagTailX0RatChunk000Sub000Block081Part003
    + surrogateDiagTailX0RatChunk000Sub000Block081Part004
    + surrogateDiagTailX0RatChunk000Sub000Block081Part005
    + surrogateDiagTailX0RatChunk000Sub000Block081Part006
    + surrogateDiagTailX0RatChunk000Sub000Block081Part007
    + surrogateDiagTailX0RatChunk000Sub000Block081Part008
    + surrogateDiagTailX0RatChunk000Sub000Block081Part009
    + surrogateDiagTailX0RatChunk000Sub000Block081Part010
    + surrogateDiagTailX0RatChunk000Sub000Block081Part011
    + surrogateDiagTailX0RatChunk000Sub000Block081Part012
    + surrogateDiagTailX0RatChunk000Sub000Block081Part013
    + surrogateDiagTailX0RatChunk000Sub000Block081Part014
    + surrogateDiagTailX0RatChunk000Sub000Block081Part015
    + surrogateDiagTailX0RatChunk000Sub000Block081Part016
    + surrogateDiagTailX0RatChunk000Sub000Block081Part017
    + surrogateDiagTailX0RatChunk000Sub000Block081Part018
    + surrogateDiagTailX0RatChunk000Sub000Block081Part019
    + surrogateDiagTailX0RatChunk000Sub000Block081Part020
    + surrogateDiagTailX0RatChunk000Sub000Block081Part021
    + surrogateDiagTailX0RatChunk000Sub000Block081Part022
    + surrogateDiagTailX0RatChunk000Sub000Block081Part023
    + surrogateDiagTailX0RatChunk000Sub000Block081Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block081_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block081Head + surrogateDiagTailX0RatChunk000Sub000Block081Mid + surrogateDiagTailX0RatChunk000Sub000Block081Tail =
      surrogateDiagTailX0RatChunk000Sub000Block081 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block081Head surrogateDiagTailX0RatChunk000Sub000Block081Mid surrogateDiagTailX0RatChunk000Sub000Block081Tail surrogateDiagTailX0RatChunk000Sub000Block081
  ring

def SurrogateDiagonalTailChunk000Sub000Block081HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block081HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block081Head

def SurrogateDiagonalTailChunk000Sub000Block081MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block081MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block081Mid

def SurrogateDiagonalTailChunk000Sub000Block081TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block081TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block081Tail

theorem surrogateDiagonalTailChunk000Sub000Block081_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block081HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block081MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block081TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block081Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block081 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block081HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block081MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block081TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block081Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block081_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
