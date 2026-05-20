import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [8,9). -/

/- Block 008 covers tail-support indices [200,225) and q from 383 to 419. -/

def TailChunk000Sub000Block008Part000SupportExplicit : Finset ℕ :=
  ([383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part000 : ℚ :=
  (59449384475 : ℚ) / 26622590673444

def SurrogateDiagonalTailChunk000Sub000Block008Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 383
    = surrogateDiagTailX0RatChunk000Sub000Block008Part000

theorem surrogateDiagonalTailChunk000Sub000Block008Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part000] using hcert

def TailChunk000Sub000Block008Part001SupportExplicit : Finset ℕ :=
  ([385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part001 : ℚ :=
  (83430641 : ℚ) / 9217843200

def SurrogateDiagonalTailChunk000Sub000Block008Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 385
    = surrogateDiagTailX0RatChunk000Sub000Block008Part001

theorem surrogateDiagonalTailChunk000Sub000Block008Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part001] using hcert

def TailChunk000Sub000Block008Part002SupportExplicit : Finset ℕ :=
  ([386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part002 : ℚ :=
  (60226976875 : ℚ) / 3398065717248

def SurrogateDiagonalTailChunk000Sub000Block008Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 386
    = surrogateDiagTailX0RatChunk000Sub000Block008Part002

theorem surrogateDiagonalTailChunk000Sub000Block008Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part002] using hcert

def TailChunk000Sub000Block008Part003SupportExplicit : Finset ℕ :=
  ([389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part003 : ℚ :=
  (61326618275 : ℚ) / 28335035793984

def SurrogateDiagonalTailChunk000Sub000Block008Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 389
    = surrogateDiagTailX0RatChunk000Sub000Block008Part003

theorem surrogateDiagonalTailChunk000Sub000Block008Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part003] using hcert

def TailChunk000Sub000Block008Part004SupportExplicit : Finset ℕ :=
  ([390] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part004 : ℚ :=
  (7439092375 : ℚ) / 53094776832

def SurrogateDiagonalTailChunk000Sub000Block008Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 390
    = surrogateDiagTailX0RatChunk000Sub000Block008Part004

theorem surrogateDiagonalTailChunk000Sub000Block008Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part004] using hcert

def TailChunk000Sub000Block008Part005SupportExplicit : Finset ℕ :=
  ([391] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part005 : ℚ :=
  (111642648775 : ℚ) / 38388179140608

def SurrogateDiagonalTailChunk000Sub000Block008Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 391
    = surrogateDiagTailX0RatChunk000Sub000Block008Part005

theorem surrogateDiagonalTailChunk000Sub000Block008Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part005] using hcert

def TailChunk000Sub000Block008Part006SupportExplicit : Finset ℕ :=
  ([393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part006 : ℚ :=
  (1575957971 : ℚ) / 228533697600

def SurrogateDiagonalTailChunk000Sub000Block008Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 393
    = surrogateDiagTailX0RatChunk000Sub000Block008Part006

theorem surrogateDiagonalTailChunk000Sub000Block008Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part006] using hcert

def TailChunk000Sub000Block008Part007SupportExplicit : Finset ℕ :=
  ([394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part007 : ℚ :=
  (7543499375 : ℚ) / 461276316816

def SurrogateDiagonalTailChunk000Sub000Block008Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 394
    = surrogateDiagTailX0RatChunk000Sub000Block008Part007

theorem surrogateDiagonalTailChunk000Sub000Block008Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part007] using hcert

def TailChunk000Sub000Block008Part008SupportExplicit : Finset ℕ :=
  ([395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part008 : ℚ :=
  (99358946425 : ℚ) / 23694373767168

def SurrogateDiagonalTailChunk000Sub000Block008Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 395
    = surrogateDiagTailX0RatChunk000Sub000Block008Part008

theorem surrogateDiagonalTailChunk000Sub000Block008Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part008] using hcert

def TailChunk000Sub000Block008Part009SupportExplicit : Finset ℕ :=
  ([397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part009 : ℚ :=
  (63874987475 : ℚ) / 30745220134464

def SurrogateDiagonalTailChunk000Sub000Block008Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 397
    = surrogateDiagTailX0RatChunk000Sub000Block008Part009

theorem surrogateDiagonalTailChunk000Sub000Block008Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part009] using hcert

def TailChunk000Sub000Block008Part010SupportExplicit : Finset ℕ :=
  ([398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part010 : ℚ :=
  (7697444375 : ℚ) / 480394064601

def SurrogateDiagonalTailChunk000Sub000Block008Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 398
    = surrogateDiagTailX0RatChunk000Sub000Block008Part010

theorem surrogateDiagonalTailChunk000Sub000Block008Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part010] using hcert

def TailChunk000Sub000Block008Part011SupportExplicit : Finset ℕ :=
  ([399] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part011 : ℚ :=
  (32989827275 : ℚ) / 2721522115584

def SurrogateDiagonalTailChunk000Sub000Block008Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 399
    = surrogateDiagTailX0RatChunk000Sub000Block008Part011

theorem surrogateDiagonalTailChunk000Sub000Block008Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part011] using hcert

def TailChunk000Sub000Block008Part012SupportExplicit : Finset ℕ :=
  ([401] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part012 : ℚ :=
  (2606745011 : ℚ) / 1280256000000

def SurrogateDiagonalTailChunk000Sub000Block008Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 401
    = surrogateDiagTailX0RatChunk000Sub000Block008Part012

theorem surrogateDiagonalTailChunk000Sub000Block008Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part012] using hcert

def TailChunk000Sub000Block008Part013SupportExplicit : Finset ℕ :=
  ([402] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part013 : ℚ :=
  (1381775 : ℚ) / 25299648

def SurrogateDiagonalTailChunk000Sub000Block008Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 402
    = surrogateDiagTailX0RatChunk000Sub000Block008Part013

theorem surrogateDiagonalTailChunk000Sub000Block008Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part013] using hcert

def TailChunk000Sub000Block008Part014SupportExplicit : Finset ℕ :=
  ([403] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part014 : ℚ :=
  (93819965 : ℚ) / 33599038464

def SurrogateDiagonalTailChunk000Sub000Block008Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 403
    = surrogateDiagTailX0RatChunk000Sub000Block008Part014

theorem surrogateDiagonalTailChunk000Sub000Block008Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part014] using hcert

def TailChunk000Sub000Block008Part015SupportExplicit : Finset ℕ :=
  ([406] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part015 : ℚ :=
  (51409307725 : ℚ) / 1991883737088

def SurrogateDiagonalTailChunk000Sub000Block008Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 406
    = surrogateDiagTailX0RatChunk000Sub000Block008Part015

theorem surrogateDiagonalTailChunk000Sub000Block008Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part015] using hcert

def TailChunk000Sub000Block008Part016SupportExplicit : Finset ℕ :=
  ([407] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part016 : ℚ :=
  (4409202553 : ℚ) / 1679951923200

def SurrogateDiagonalTailChunk000Sub000Block008Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 407
    = surrogateDiagTailX0RatChunk000Sub000Block008Part016

theorem surrogateDiagonalTailChunk000Sub000Block008Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part016] using hcert

def TailChunk000Sub000Block008Part017SupportExplicit : Finset ℕ :=
  ([409] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part017 : ℚ :=
  (6954707575 : ℚ) / 3849417409536

def SurrogateDiagonalTailChunk000Sub000Block008Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 409
    = surrogateDiagTailX0RatChunk000Sub000Block008Part017

theorem surrogateDiagonalTailChunk000Sub000Block008Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part017] using hcert

def TailChunk000Sub000Block008Part018SupportExplicit : Finset ℕ :=
  ([410] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part018 : ℚ :=
  (1977226669 : ℚ) / 65549107200

def SurrogateDiagonalTailChunk000Sub000Block008Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 410
    = surrogateDiagTailX0RatChunk000Sub000Block008Part018

theorem surrogateDiagonalTailChunk000Sub000Block008Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part018] using hcert

def TailChunk000Sub000Block008Part019SupportExplicit : Finset ℕ :=
  ([411] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part019 : ℚ :=
  (1328520775 : ℚ) / 213856522752

def SurrogateDiagonalTailChunk000Sub000Block008Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 411
    = surrogateDiagTailX0RatChunk000Sub000Block008Part019

theorem surrogateDiagonalTailChunk000Sub000Block008Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part019] using hcert

def TailChunk000Sub000Block008Part020SupportExplicit : Finset ℕ :=
  ([413] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part020 : ℚ :=
  (108040689625 : ℚ) / 36672780129408

def SurrogateDiagonalTailChunk000Sub000Block008Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 413
    = surrogateDiagTailX0RatChunk000Sub000Block008Part020

theorem surrogateDiagonalTailChunk000Sub000Block008Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part020] using hcert

def TailChunk000Sub000Block008Part021SupportExplicit : Finset ℕ :=
  ([415] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part021 : ℚ :=
  (12764552375 : ℚ) / 3617697474816

def SurrogateDiagonalTailChunk000Sub000Block008Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 415
    = surrogateDiagTailX0RatChunk000Sub000Block008Part021

theorem surrogateDiagonalTailChunk000Sub000Block008Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part021] using hcert

def TailChunk000Sub000Block008Part022SupportExplicit : Finset ℕ :=
  ([417] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part022 : ℚ :=
  (5754575 : ℚ) / 967130496

def SurrogateDiagonalTailChunk000Sub000Block008Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 417
    = surrogateDiagTailX0RatChunk000Sub000Block008Part022

theorem surrogateDiagonalTailChunk000Sub000Block008Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part022] using hcert

def TailChunk000Sub000Block008Part023SupportExplicit : Finset ℕ :=
  ([418] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part023 : ℚ :=
  (752186203 : ℚ) / 34998998400

def SurrogateDiagonalTailChunk000Sub000Block008Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 418
    = surrogateDiagTailX0RatChunk000Sub000Block008Part023

theorem surrogateDiagonalTailChunk000Sub000Block008Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part023] using hcert

def TailChunk000Sub000Block008Part024SupportExplicit : Finset ℕ :=
  ([419] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block008Part024 : ℚ :=
  (21896845725 : ℚ) / 12722742446348

def SurrogateDiagonalTailChunk000Sub000Block008Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 419
    = surrogateDiagTailX0RatChunk000Sub000Block008Part024

theorem surrogateDiagonalTailChunk000Sub000Block008Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block008Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block008Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block008Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block008Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block008Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block008HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block008Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block008Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block008Part000
    + surrogateDiagTailX0RatChunk000Sub000Block008Part001
    + surrogateDiagTailX0RatChunk000Sub000Block008Part002
    + surrogateDiagTailX0RatChunk000Sub000Block008Part003
    + surrogateDiagTailX0RatChunk000Sub000Block008Part004
    + surrogateDiagTailX0RatChunk000Sub000Block008Part005
    + surrogateDiagTailX0RatChunk000Sub000Block008Part006
    + surrogateDiagTailX0RatChunk000Sub000Block008Part007
    + surrogateDiagTailX0RatChunk000Sub000Block008Part008
    + surrogateDiagTailX0RatChunk000Sub000Block008Part009

def surrogateDiagonalTailChunk000Sub000Block008MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block008Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block008Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block008Part010
    + surrogateDiagTailX0RatChunk000Sub000Block008Part011
    + surrogateDiagTailX0RatChunk000Sub000Block008Part012
    + surrogateDiagTailX0RatChunk000Sub000Block008Part013
    + surrogateDiagTailX0RatChunk000Sub000Block008Part014
    + surrogateDiagTailX0RatChunk000Sub000Block008Part015
    + surrogateDiagTailX0RatChunk000Sub000Block008Part016
    + surrogateDiagTailX0RatChunk000Sub000Block008Part017
    + surrogateDiagTailX0RatChunk000Sub000Block008Part018
    + surrogateDiagTailX0RatChunk000Sub000Block008Part019

def surrogateDiagonalTailChunk000Sub000Block008TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block008Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block008Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block008Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block008Part020
    + surrogateDiagTailX0RatChunk000Sub000Block008Part021
    + surrogateDiagTailX0RatChunk000Sub000Block008Part022
    + surrogateDiagTailX0RatChunk000Sub000Block008Part023
    + surrogateDiagTailX0RatChunk000Sub000Block008Part024

def surrogateDiagonalTailChunk000Sub000Block008Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block008HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block008MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block008TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block008 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block008Part000
    + surrogateDiagTailX0RatChunk000Sub000Block008Part001
    + surrogateDiagTailX0RatChunk000Sub000Block008Part002
    + surrogateDiagTailX0RatChunk000Sub000Block008Part003
    + surrogateDiagTailX0RatChunk000Sub000Block008Part004
    + surrogateDiagTailX0RatChunk000Sub000Block008Part005
    + surrogateDiagTailX0RatChunk000Sub000Block008Part006
    + surrogateDiagTailX0RatChunk000Sub000Block008Part007
    + surrogateDiagTailX0RatChunk000Sub000Block008Part008
    + surrogateDiagTailX0RatChunk000Sub000Block008Part009
    + surrogateDiagTailX0RatChunk000Sub000Block008Part010
    + surrogateDiagTailX0RatChunk000Sub000Block008Part011
    + surrogateDiagTailX0RatChunk000Sub000Block008Part012
    + surrogateDiagTailX0RatChunk000Sub000Block008Part013
    + surrogateDiagTailX0RatChunk000Sub000Block008Part014
    + surrogateDiagTailX0RatChunk000Sub000Block008Part015
    + surrogateDiagTailX0RatChunk000Sub000Block008Part016
    + surrogateDiagTailX0RatChunk000Sub000Block008Part017
    + surrogateDiagTailX0RatChunk000Sub000Block008Part018
    + surrogateDiagTailX0RatChunk000Sub000Block008Part019
    + surrogateDiagTailX0RatChunk000Sub000Block008Part020
    + surrogateDiagTailX0RatChunk000Sub000Block008Part021
    + surrogateDiagTailX0RatChunk000Sub000Block008Part022
    + surrogateDiagTailX0RatChunk000Sub000Block008Part023
    + surrogateDiagTailX0RatChunk000Sub000Block008Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block008_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block008Head + surrogateDiagTailX0RatChunk000Sub000Block008Mid + surrogateDiagTailX0RatChunk000Sub000Block008Tail =
      surrogateDiagTailX0RatChunk000Sub000Block008 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block008Head surrogateDiagTailX0RatChunk000Sub000Block008Mid surrogateDiagTailX0RatChunk000Sub000Block008Tail surrogateDiagTailX0RatChunk000Sub000Block008
  ring

def SurrogateDiagonalTailChunk000Sub000Block008HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block008HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block008Head

def SurrogateDiagonalTailChunk000Sub000Block008MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block008MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block008Mid

def SurrogateDiagonalTailChunk000Sub000Block008TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block008TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block008Tail

theorem surrogateDiagonalTailChunk000Sub000Block008_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block008HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block008MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block008TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block008Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block008 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block008HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block008MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block008TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block008Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block008_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
