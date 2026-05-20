import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [129,130). -/

/- Block 129 covers tail-support indices [3225,3250) and q from 5359 to 5398. -/

def TailChunk000Sub000Block129Part000SupportExplicit : Finset ℕ :=
  ([5359] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part000 : ℚ :=
  (568664026575 : ℚ) / 565650619390590976

def SurrogateDiagonalTailChunk000Sub000Block129Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5359
    = surrogateDiagTailX0RatChunk000Sub000Block129Part000

theorem surrogateDiagonalTailChunk000Sub000Block129Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part000] using hcert

def TailChunk000Sub000Block129Part001SupportExplicit : Finset ℕ :=
  ([5361] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part001 : ℚ :=
  (119679825 : ℚ) / 40699194086464

def SurrogateDiagonalTailChunk000Sub000Block129Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5361
    = surrogateDiagTailX0RatChunk000Sub000Block129Part001

theorem surrogateDiagonalTailChunk000Sub000Block129Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part001] using hcert

def TailChunk000Sub000Block129Part002SupportExplicit : Finset ℕ :=
  ([5362] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part002 : ℚ :=
  (379499953775 : ℚ) / 34502877512783424

def SurrogateDiagonalTailChunk000Sub000Block129Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5362
    = surrogateDiagTailX0RatChunk000Sub000Block129Part002

theorem surrogateDiagonalTailChunk000Sub000Block129Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part002] using hcert

def TailChunk000Sub000Block129Part003SupportExplicit : Finset ℕ :=
  ([5363] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part003 : ℚ :=
  (34510324007 : ℚ) / 35453217993753600

def SurrogateDiagonalTailChunk000Sub000Block129Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5363
    = surrogateDiagTailX0RatChunk000Sub000Block129Part003

theorem surrogateDiagonalTailChunk000Sub000Block129Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part003] using hcert

def TailChunk000Sub000Block129Part004SupportExplicit : Finset ℕ :=
  ([5365] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part004 : ℚ :=
  (1346082989725 : ℚ) / 660859218756108288

def SurrogateDiagonalTailChunk000Sub000Block129Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5365
    = surrogateDiagTailX0RatChunk000Sub000Block129Part004

theorem surrogateDiagonalTailChunk000Sub000Block129Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part004] using hcert

def TailChunk000Sub000Block129Part005SupportExplicit : Finset ℕ :=
  ([5366] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part005 : ℚ :=
  (899631162775 : ℚ) / 129378452714879688

def SurrogateDiagonalTailChunk000Sub000Block129Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5366
    = surrogateDiagTailX0RatChunk000Sub000Block129Part005

theorem surrogateDiagonalTailChunk000Sub000Block129Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part005] using hcert

def TailChunk000Sub000Block129Part006SupportExplicit : Finset ℕ :=
  ([5367] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part006 : ℚ :=
  (39982625 : ℚ) / 13627267918848

def SurrogateDiagonalTailChunk000Sub000Block129Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5367
    = surrogateDiagTailX0RatChunk000Sub000Block129Part006

theorem surrogateDiagonalTailChunk000Sub000Block129Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part006] using hcert

def TailChunk000Sub000Block129Part007SupportExplicit : Finset ℕ :=
  ([5369] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part007 : ℚ :=
  (1391329045975 : ℚ) / 760446768763404288

def SurrogateDiagonalTailChunk000Sub000Block129Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5369
    = surrogateDiagTailX0RatChunk000Sub000Block129Part007

theorem surrogateDiagonalTailChunk000Sub000Block129Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part007] using hcert

def TailChunk000Sub000Block129Part008SupportExplicit : Finset ℕ :=
  ([5370] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part008 : ℚ :=
  (155979103275 : ℚ) / 3427248234397696

def SurrogateDiagonalTailChunk000Sub000Block129Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5370
    = surrogateDiagTailX0RatChunk000Sub000Block129Part008

theorem surrogateDiagonalTailChunk000Sub000Block129Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part008] using hcert

def TailChunk000Sub000Block129Part009SupportExplicit : Finset ℕ :=
  ([5371] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part009 : ℚ :=
  (69673210039 : ℚ) / 73130783232000000

def SurrogateDiagonalTailChunk000Sub000Block129Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5371
    = surrogateDiagTailX0RatChunk000Sub000Block129Part009

theorem surrogateDiagonalTailChunk000Sub000Block129Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part009] using hcert

def TailChunk000Sub000Block129Part010SupportExplicit : Finset ℕ :=
  ([5374] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part010 : ℚ :=
  (112812015625 : ℚ) / 32538003451440402

def SurrogateDiagonalTailChunk000Sub000Block129Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5374
    = surrogateDiagTailX0RatChunk000Sub000Block129Part010

theorem surrogateDiagonalTailChunk000Sub000Block129Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part010] using hcert

def TailChunk000Sub000Block129Part011SupportExplicit : Finset ℕ :=
  ([5377] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part011 : ℚ :=
  (850397437025 : ℚ) / 830009984905940544

def SurrogateDiagonalTailChunk000Sub000Block129Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5377
    = surrogateDiagTailX0RatChunk000Sub000Block129Part011

theorem surrogateDiagonalTailChunk000Sub000Block129Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part011] using hcert

def TailChunk000Sub000Block129Part012SupportExplicit : Finset ℕ :=
  ([5378] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part012 : ℚ :=
  (903659356975 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block129Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5378
    = surrogateDiagTailX0RatChunk000Sub000Block129Part012

theorem surrogateDiagonalTailChunk000Sub000Block129Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part012] using hcert

def TailChunk000Sub000Block129Part013SupportExplicit : Finset ℕ :=
  ([5379] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part013 : ℚ :=
  (21616011563 : ℚ) / 5511082284057600

def SurrogateDiagonalTailChunk000Sub000Block129Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5379
    = surrogateDiagTailX0RatChunk000Sub000Block129Part013

theorem surrogateDiagonalTailChunk000Sub000Block129Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part013] using hcert

def TailChunk000Sub000Block129Part014SupportExplicit : Finset ℕ :=
  ([5381] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part014 : ℚ :=
  (723879025 : ℚ) / 837945847018272

def SurrogateDiagonalTailChunk000Sub000Block129Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5381
    = surrogateDiagTailX0RatChunk000Sub000Block129Part014

theorem surrogateDiagonalTailChunk000Sub000Block129Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part014] using hcert

def TailChunk000Sub000Block129Part015SupportExplicit : Finset ℕ :=
  ([5383] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part015 : ℚ :=
  (1513591084375 : ℚ) / 1127396651405672448

def SurrogateDiagonalTailChunk000Sub000Block129Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5383
    = surrogateDiagTailX0RatChunk000Sub000Block129Part015

theorem surrogateDiagonalTailChunk000Sub000Block129Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part015] using hcert

def TailChunk000Sub000Block129Part016SupportExplicit : Finset ℕ :=
  ([5385] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part016 : ℚ :=
  (931861586575 : ℚ) / 168235992045355008

def SurrogateDiagonalTailChunk000Sub000Block129Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5385
    = surrogateDiagTailX0RatChunk000Sub000Block129Part016

theorem surrogateDiagonalTailChunk000Sub000Block129Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part016] using hcert

def TailChunk000Sub000Block129Part017SupportExplicit : Finset ℕ :=
  ([5386] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part017 : ℚ :=
  (906349818775 : ℚ) / 131318853105157248

def SurrogateDiagonalTailChunk000Sub000Block129Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5386
    = surrogateDiagTailX0RatChunk000Sub000Block129Part017

theorem surrogateDiagonalTailChunk000Sub000Block129Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part017] using hcert

def TailChunk000Sub000Block129Part018SupportExplicit : Finset ℕ :=
  ([5387] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part018 : ℚ :=
  (453433890625 : ℚ) / 526056345811126002

def SurrogateDiagonalTailChunk000Sub000Block129Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5387
    = surrogateDiagTailX0RatChunk000Sub000Block129Part018

theorem surrogateDiagonalTailChunk000Sub000Block129Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part018] using hcert

def TailChunk000Sub000Block129Part019SupportExplicit : Finset ℕ :=
  ([5389] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part019 : ℚ :=
  (848315114225 : ℚ) / 817005771173658624

def SurrogateDiagonalTailChunk000Sub000Block129Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5389
    = surrogateDiagTailX0RatChunk000Sub000Block129Part019

theorem surrogateDiagonalTailChunk000Sub000Block129Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part019] using hcert

def TailChunk000Sub000Block129Part020SupportExplicit : Finset ℕ :=
  ([5393] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part020 : ℚ :=
  (454444515625 : ℚ) / 528404371232858112

def SurrogateDiagonalTailChunk000Sub000Block129Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5393
    = surrogateDiagTailX0RatChunk000Sub000Block129Part020

theorem surrogateDiagonalTailChunk000Sub000Block129Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part020] using hcert

def TailChunk000Sub000Block129Part021SupportExplicit : Finset ℕ :=
  ([5394] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part021 : ℚ :=
  (6927947071 : ℚ) / 265584498278400

def SurrogateDiagonalTailChunk000Sub000Block129Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5394
    = surrogateDiagTailX0RatChunk000Sub000Block129Part021

theorem surrogateDiagonalTailChunk000Sub000Block129Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part021] using hcert

def TailChunk000Sub000Block129Part022SupportExplicit : Finset ℕ :=
  ([5395] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part022 : ℚ :=
  (164732439875 : ℚ) / 75016574837784576

def SurrogateDiagonalTailChunk000Sub000Block129Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5395
    = surrogateDiagTailX0RatChunk000Sub000Block129Part022

theorem surrogateDiagonalTailChunk000Sub000Block129Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part022] using hcert

def TailChunk000Sub000Block129Part023SupportExplicit : Finset ℕ :=
  ([5397] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part023 : ℚ :=
  (1015647700975 : ℚ) / 222695634845564928

def SurrogateDiagonalTailChunk000Sub000Block129Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5397
    = surrogateDiagTailX0RatChunk000Sub000Block129Part023

theorem surrogateDiagonalTailChunk000Sub000Block129Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part023] using hcert

def TailChunk000Sub000Block129Part024SupportExplicit : Finset ℕ :=
  ([5398] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block129Part024 : ℚ :=
  (910393009975 : ℚ) / 132493520589476808

def SurrogateDiagonalTailChunk000Sub000Block129Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5398
    = surrogateDiagTailX0RatChunk000Sub000Block129Part024

theorem surrogateDiagonalTailChunk000Sub000Block129Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block129Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block129Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block129Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block129Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block129Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block129Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block129HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block129Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block129Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block129Part000
    + surrogateDiagTailX0RatChunk000Sub000Block129Part001
    + surrogateDiagTailX0RatChunk000Sub000Block129Part002
    + surrogateDiagTailX0RatChunk000Sub000Block129Part003
    + surrogateDiagTailX0RatChunk000Sub000Block129Part004
    + surrogateDiagTailX0RatChunk000Sub000Block129Part005
    + surrogateDiagTailX0RatChunk000Sub000Block129Part006
    + surrogateDiagTailX0RatChunk000Sub000Block129Part007
    + surrogateDiagTailX0RatChunk000Sub000Block129Part008
    + surrogateDiagTailX0RatChunk000Sub000Block129Part009

def surrogateDiagonalTailChunk000Sub000Block129MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block129Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block129Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block129Part010
    + surrogateDiagTailX0RatChunk000Sub000Block129Part011
    + surrogateDiagTailX0RatChunk000Sub000Block129Part012
    + surrogateDiagTailX0RatChunk000Sub000Block129Part013
    + surrogateDiagTailX0RatChunk000Sub000Block129Part014
    + surrogateDiagTailX0RatChunk000Sub000Block129Part015
    + surrogateDiagTailX0RatChunk000Sub000Block129Part016
    + surrogateDiagTailX0RatChunk000Sub000Block129Part017
    + surrogateDiagTailX0RatChunk000Sub000Block129Part018
    + surrogateDiagTailX0RatChunk000Sub000Block129Part019

def surrogateDiagonalTailChunk000Sub000Block129TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block129Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block129Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block129Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block129Part020
    + surrogateDiagTailX0RatChunk000Sub000Block129Part021
    + surrogateDiagTailX0RatChunk000Sub000Block129Part022
    + surrogateDiagTailX0RatChunk000Sub000Block129Part023
    + surrogateDiagTailX0RatChunk000Sub000Block129Part024

def surrogateDiagonalTailChunk000Sub000Block129Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block129HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block129MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block129TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block129 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block129Part000
    + surrogateDiagTailX0RatChunk000Sub000Block129Part001
    + surrogateDiagTailX0RatChunk000Sub000Block129Part002
    + surrogateDiagTailX0RatChunk000Sub000Block129Part003
    + surrogateDiagTailX0RatChunk000Sub000Block129Part004
    + surrogateDiagTailX0RatChunk000Sub000Block129Part005
    + surrogateDiagTailX0RatChunk000Sub000Block129Part006
    + surrogateDiagTailX0RatChunk000Sub000Block129Part007
    + surrogateDiagTailX0RatChunk000Sub000Block129Part008
    + surrogateDiagTailX0RatChunk000Sub000Block129Part009
    + surrogateDiagTailX0RatChunk000Sub000Block129Part010
    + surrogateDiagTailX0RatChunk000Sub000Block129Part011
    + surrogateDiagTailX0RatChunk000Sub000Block129Part012
    + surrogateDiagTailX0RatChunk000Sub000Block129Part013
    + surrogateDiagTailX0RatChunk000Sub000Block129Part014
    + surrogateDiagTailX0RatChunk000Sub000Block129Part015
    + surrogateDiagTailX0RatChunk000Sub000Block129Part016
    + surrogateDiagTailX0RatChunk000Sub000Block129Part017
    + surrogateDiagTailX0RatChunk000Sub000Block129Part018
    + surrogateDiagTailX0RatChunk000Sub000Block129Part019
    + surrogateDiagTailX0RatChunk000Sub000Block129Part020
    + surrogateDiagTailX0RatChunk000Sub000Block129Part021
    + surrogateDiagTailX0RatChunk000Sub000Block129Part022
    + surrogateDiagTailX0RatChunk000Sub000Block129Part023
    + surrogateDiagTailX0RatChunk000Sub000Block129Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block129_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block129Head + surrogateDiagTailX0RatChunk000Sub000Block129Mid + surrogateDiagTailX0RatChunk000Sub000Block129Tail =
      surrogateDiagTailX0RatChunk000Sub000Block129 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block129Head surrogateDiagTailX0RatChunk000Sub000Block129Mid surrogateDiagTailX0RatChunk000Sub000Block129Tail surrogateDiagTailX0RatChunk000Sub000Block129
  ring

def SurrogateDiagonalTailChunk000Sub000Block129HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block129HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block129Head

def SurrogateDiagonalTailChunk000Sub000Block129MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block129MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block129Mid

def SurrogateDiagonalTailChunk000Sub000Block129TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block129TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block129Tail

theorem surrogateDiagonalTailChunk000Sub000Block129_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block129HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block129MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block129TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block129Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block129 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block129HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block129MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block129TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block129Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block129_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
