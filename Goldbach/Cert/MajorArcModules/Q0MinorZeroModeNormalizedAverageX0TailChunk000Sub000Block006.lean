import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [6,7). -/

/- Block 006 covers tail-support indices [150,175) and q from 298 to 335. -/

def TailChunk000Sub000Block006Part000SupportExplicit : Finset ℕ :=
  ([298] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part000 : ℚ :=
  (46865755975 : ℚ) / 1199702932608

def SurrogateDiagonalTailChunk000Sub000Block006Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 298
    = surrogateDiagTailX0RatChunk000Sub000Block006Part000

theorem surrogateDiagonalTailChunk000Sub000Block006Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part000] using hcert

def TailChunk000Sub000Block006Part001SupportExplicit : Finset ℕ :=
  ([299] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part001 : ℚ :=
  (7217136875 : ℚ) / 1104205436928

def SurrogateDiagonalTailChunk000Sub000Block006Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 299
    = surrogateDiagTailX0RatChunk000Sub000Block006Part001

theorem surrogateDiagonalTailChunk000Sub000Block006Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part001] using hcert

def TailChunk000Sub000Block006Part002SupportExplicit : Finset ℕ :=
  ([301] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part002 : ℚ :=
  (76486107475 : ℚ) / 10083911419008

def SurrogateDiagonalTailChunk000Sub000Block006Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 301
    = surrogateDiagTailX0RatChunk000Sub000Block006Part002

theorem surrogateDiagonalTailChunk000Sub000Block006Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part002] using hcert

def TailChunk000Sub000Block006Part003SupportExplicit : Finset ℕ :=
  ([302] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part003 : ℚ :=
  (5768653 : ℚ) / 156281250

def SurrogateDiagonalTailChunk000Sub000Block006Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 302
    = surrogateDiagTailX0RatChunk000Sub000Block006Part003

theorem surrogateDiagonalTailChunk000Sub000Block006Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part003] using hcert

def TailChunk000Sub000Block006Part004SupportExplicit : Finset ℕ :=
  ([303] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part004 : ℚ :=
  (49504691 : ℚ) / 3200640000

def SurrogateDiagonalTailChunk000Sub000Block006Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 303
    = surrogateDiagTailX0RatChunk000Sub000Block006Part004

theorem surrogateDiagonalTailChunk000Sub000Block006Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part004] using hcert

def TailChunk000Sub000Block006Part005SupportExplicit : Finset ℕ :=
  ([305] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part005 : ℚ :=
  (982605503 : ℚ) / 110614118400

def SurrogateDiagonalTailChunk000Sub000Block006Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 305
    = surrogateDiagTailX0RatChunk000Sub000Block006Part005

theorem surrogateDiagonalTailChunk000Sub000Block006Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part005] using hcert

def TailChunk000Sub000Block006Part006SupportExplicit : Finset ℕ :=
  ([307] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part006 : ℚ :=
  (11745781625 : ℚ) / 2740454386281

def SurrogateDiagonalTailChunk000Sub000Block006Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 307
    = surrogateDiagTailX0RatChunk000Sub000Block006Part006

theorem surrogateDiagonalTailChunk000Sub000Block006Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part006] using hcert

def TailChunk000Sub000Block006Part007SupportExplicit : Finset ℕ :=
  ([309] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part007 : ℚ :=
  (4202875 : ℚ) / 288648576

def SurrogateDiagonalTailChunk000Sub000Block006Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 309
    = surrogateDiagTailX0RatChunk000Sub000Block006Part007

theorem surrogateDiagonalTailChunk000Sub000Block006Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part007] using hcert

def TailChunk000Sub000Block006Part008SupportExplicit : Finset ℕ :=
  ([310] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part008 : ℚ :=
  (6352907 : ℚ) / 86417280

def SurrogateDiagonalTailChunk000Sub000Block006Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 310
    = surrogateDiagTailX0RatChunk000Sub000Block006Part008

theorem surrogateDiagonalTailChunk000Sub000Block006Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part008] using hcert

def TailChunk000Sub000Block006Part009SupportExplicit : Finset ℕ :=
  ([311] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part009 : ℚ :=
  (96430837 : ℚ) / 23092642605

def SurrogateDiagonalTailChunk000Sub000Block006Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 311
    = surrogateDiagTailX0RatChunk000Sub000Block006Part009

theorem surrogateDiagonalTailChunk000Sub000Block006Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part009] using hcert

def TailChunk000Sub000Block006Part010SupportExplicit : Finset ℕ :=
  ([313] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part010 : ℚ :=
  (12209386625 : ℚ) / 2961796720896

def SurrogateDiagonalTailChunk000Sub000Block006Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 313
    = surrogateDiagTailX0RatChunk000Sub000Block006Part010

theorem surrogateDiagonalTailChunk000Sub000Block006Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part010] using hcert

def TailChunk000Sub000Block006Part011SupportExplicit : Finset ℕ :=
  ([314] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part011 : ℚ :=
  (3062022025 : ℚ) / 92556147528

def SurrogateDiagonalTailChunk000Sub000Block006Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 314
    = surrogateDiagTailX0RatChunk000Sub000Block006Part011

theorem surrogateDiagonalTailChunk000Sub000Block006Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part011] using hcert

def TailChunk000Sub000Block006Part012SupportExplicit : Finset ℕ :=
  ([317] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part012 : ℚ :=
  (12523441625 : ℚ) / 3116629681296

def SurrogateDiagonalTailChunk000Sub000Block006Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 317
    = surrogateDiagTailX0RatChunk000Sub000Block006Part012

theorem surrogateDiagonalTailChunk000Sub000Block006Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part012] using hcert

def TailChunk000Sub000Block006Part013SupportExplicit : Finset ℕ :=
  ([318] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part013 : ℚ :=
  (32898730825 : ℚ) / 292523132928

def SurrogateDiagonalTailChunk000Sub000Block006Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 318
    = surrogateDiagTailX0RatChunk000Sub000Block006Part013

theorem surrogateDiagonalTailChunk000Sub000Block006Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part013] using hcert

def TailChunk000Sub000Block006Part014SupportExplicit : Finset ℕ :=
  ([319] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part014 : ℚ :=
  (142527649 : ℚ) / 24591157248

def SurrogateDiagonalTailChunk000Sub000Block006Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 319
    = surrogateDiagTailX0RatChunk000Sub000Block006Part014

theorem surrogateDiagonalTailChunk000Sub000Block006Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part014] using hcert

def TailChunk000Sub000Block006Part015SupportExplicit : Finset ℕ :=
  ([321] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part015 : ℚ :=
  (67346260975 : ℚ) / 5050917821568

def SurrogateDiagonalTailChunk000Sub000Block006Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 321
    = surrogateDiagTailX0RatChunk000Sub000Block006Part015

theorem surrogateDiagonalTailChunk000Sub000Block006Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part015] using hcert

def TailChunk000Sub000Block006Part016SupportExplicit : Finset ℕ :=
  ([322] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part016 : ℚ :=
  (1144077725 : ℚ) / 21087256608

def SurrogateDiagonalTailChunk000Sub000Block006Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 322
    = surrogateDiagTailX0RatChunk000Sub000Block006Part016

theorem surrogateDiagonalTailChunk000Sub000Block006Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part016] using hcert

def TailChunk000Sub000Block006Part017SupportExplicit : Finset ℕ :=
  ([323] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part017 : ℚ :=
  (15448442675 : ℚ) / 2867117948928

def SurrogateDiagonalTailChunk000Sub000Block006Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 323
    = surrogateDiagTailX0RatChunk000Sub000Block006Part017

theorem surrogateDiagonalTailChunk000Sub000Block006Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part017] using hcert

def TailChunk000Sub000Block006Part018SupportExplicit : Finset ℕ :=
  ([326] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part018 : ℚ :=
  (51168572875 : ℚ) / 1722213213768

def SurrogateDiagonalTailChunk000Sub000Block006Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 326
    = surrogateDiagTailX0RatChunk000Sub000Block006Part018

theorem surrogateDiagonalTailChunk000Sub000Block006Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part018] using hcert

def TailChunk000Sub000Block006Part019SupportExplicit : Finset ℕ :=
  ([327] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part019 : ℚ :=
  (66971680675 : ℚ) / 5443044231168

def SurrogateDiagonalTailChunk000Sub000Block006Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 327
    = surrogateDiagTailX0RatChunk000Sub000Block006Part019

theorem surrogateDiagonalTailChunk000Sub000Block006Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part019] using hcert

def TailChunk000Sub000Block006Part020SupportExplicit : Finset ℕ :=
  ([329] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part020 : ℚ :=
  (42650891375 : ℚ) / 7254929415744

def SurrogateDiagonalTailChunk000Sub000Block006Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 329
    = surrogateDiagTailX0RatChunk000Sub000Block006Part020

theorem surrogateDiagonalTailChunk000Sub000Block006Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part020] using hcert

def TailChunk000Sub000Block006Part021SupportExplicit : Finset ℕ :=
  ([330] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part021 : ℚ :=
  (6235237 : ℚ) / 25605120

def SurrogateDiagonalTailChunk000Sub000Block006Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 330
    = surrogateDiagTailX0RatChunk000Sub000Block006Part021

theorem surrogateDiagonalTailChunk000Sub000Block006Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part021] using hcert

def TailChunk000Sub000Block006Part022SupportExplicit : Finset ℕ :=
  ([331] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part022 : ℚ :=
  (30348397 : ℚ) / 8786356920

def SurrogateDiagonalTailChunk000Sub000Block006Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 331
    = surrogateDiagTailX0RatChunk000Sub000Block006Part022

theorem surrogateDiagonalTailChunk000Sub000Block006Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part022] using hcert

def TailChunk000Sub000Block006Part023SupportExplicit : Finset ℕ :=
  ([334] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part023 : ℚ :=
  (25132869575 : ℚ) / 949356253284

def SurrogateDiagonalTailChunk000Sub000Block006Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 334
    = surrogateDiagTailX0RatChunk000Sub000Block006Part023

theorem surrogateDiagonalTailChunk000Sub000Block006Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part023] using hcert

def TailChunk000Sub000Block006Part024SupportExplicit : Finset ℕ :=
  ([335] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block006Part024 : ℚ :=
  (41461915625 : ℚ) / 6073129903104

def SurrogateDiagonalTailChunk000Sub000Block006Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 335
    = surrogateDiagTailX0RatChunk000Sub000Block006Part024

theorem surrogateDiagonalTailChunk000Sub000Block006Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block006Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block006Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block006Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block006Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block006Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block006HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block006Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block006Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block006Part000
    + surrogateDiagTailX0RatChunk000Sub000Block006Part001
    + surrogateDiagTailX0RatChunk000Sub000Block006Part002
    + surrogateDiagTailX0RatChunk000Sub000Block006Part003
    + surrogateDiagTailX0RatChunk000Sub000Block006Part004
    + surrogateDiagTailX0RatChunk000Sub000Block006Part005
    + surrogateDiagTailX0RatChunk000Sub000Block006Part006
    + surrogateDiagTailX0RatChunk000Sub000Block006Part007
    + surrogateDiagTailX0RatChunk000Sub000Block006Part008
    + surrogateDiagTailX0RatChunk000Sub000Block006Part009

def surrogateDiagonalTailChunk000Sub000Block006MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block006Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block006Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block006Part010
    + surrogateDiagTailX0RatChunk000Sub000Block006Part011
    + surrogateDiagTailX0RatChunk000Sub000Block006Part012
    + surrogateDiagTailX0RatChunk000Sub000Block006Part013
    + surrogateDiagTailX0RatChunk000Sub000Block006Part014
    + surrogateDiagTailX0RatChunk000Sub000Block006Part015
    + surrogateDiagTailX0RatChunk000Sub000Block006Part016
    + surrogateDiagTailX0RatChunk000Sub000Block006Part017
    + surrogateDiagTailX0RatChunk000Sub000Block006Part018
    + surrogateDiagTailX0RatChunk000Sub000Block006Part019

def surrogateDiagonalTailChunk000Sub000Block006TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block006Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block006Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block006Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block006Part020
    + surrogateDiagTailX0RatChunk000Sub000Block006Part021
    + surrogateDiagTailX0RatChunk000Sub000Block006Part022
    + surrogateDiagTailX0RatChunk000Sub000Block006Part023
    + surrogateDiagTailX0RatChunk000Sub000Block006Part024

def surrogateDiagonalTailChunk000Sub000Block006Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block006HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block006MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block006TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block006 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block006Part000
    + surrogateDiagTailX0RatChunk000Sub000Block006Part001
    + surrogateDiagTailX0RatChunk000Sub000Block006Part002
    + surrogateDiagTailX0RatChunk000Sub000Block006Part003
    + surrogateDiagTailX0RatChunk000Sub000Block006Part004
    + surrogateDiagTailX0RatChunk000Sub000Block006Part005
    + surrogateDiagTailX0RatChunk000Sub000Block006Part006
    + surrogateDiagTailX0RatChunk000Sub000Block006Part007
    + surrogateDiagTailX0RatChunk000Sub000Block006Part008
    + surrogateDiagTailX0RatChunk000Sub000Block006Part009
    + surrogateDiagTailX0RatChunk000Sub000Block006Part010
    + surrogateDiagTailX0RatChunk000Sub000Block006Part011
    + surrogateDiagTailX0RatChunk000Sub000Block006Part012
    + surrogateDiagTailX0RatChunk000Sub000Block006Part013
    + surrogateDiagTailX0RatChunk000Sub000Block006Part014
    + surrogateDiagTailX0RatChunk000Sub000Block006Part015
    + surrogateDiagTailX0RatChunk000Sub000Block006Part016
    + surrogateDiagTailX0RatChunk000Sub000Block006Part017
    + surrogateDiagTailX0RatChunk000Sub000Block006Part018
    + surrogateDiagTailX0RatChunk000Sub000Block006Part019
    + surrogateDiagTailX0RatChunk000Sub000Block006Part020
    + surrogateDiagTailX0RatChunk000Sub000Block006Part021
    + surrogateDiagTailX0RatChunk000Sub000Block006Part022
    + surrogateDiagTailX0RatChunk000Sub000Block006Part023
    + surrogateDiagTailX0RatChunk000Sub000Block006Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block006_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block006Head + surrogateDiagTailX0RatChunk000Sub000Block006Mid + surrogateDiagTailX0RatChunk000Sub000Block006Tail =
      surrogateDiagTailX0RatChunk000Sub000Block006 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block006Head surrogateDiagTailX0RatChunk000Sub000Block006Mid surrogateDiagTailX0RatChunk000Sub000Block006Tail surrogateDiagTailX0RatChunk000Sub000Block006
  ring

def SurrogateDiagonalTailChunk000Sub000Block006HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block006HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block006Head

def SurrogateDiagonalTailChunk000Sub000Block006MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block006MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block006Mid

def SurrogateDiagonalTailChunk000Sub000Block006TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block006TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block006Tail

theorem surrogateDiagonalTailChunk000Sub000Block006_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block006HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block006MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block006TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block006Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block006 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block006HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block006MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block006TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block006Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block006_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
