import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [110,111). -/

/- Block 110 covers tail-support indices [2750,2775) and q from 4573 to 4613. -/

def TailChunk000Sub000Block110Part000SupportExplicit : Finset ℕ :=
  ([4573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part000 : ℚ :=
  (308802619525 : ℚ) / 211342078500667392

def SurrogateDiagonalTailChunk000Sub000Block110Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4573
    = surrogateDiagTailX0RatChunk000Sub000Block110Part000

theorem surrogateDiagonalTailChunk000Sub000Block110Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part000] using hcert

def TailChunk000Sub000Block110Part001SupportExplicit : Finset ℕ :=
  ([4574] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part001 : ℚ :=
  (653665365775 : ℚ) / 68286014055956808

def SurrogateDiagonalTailChunk000Sub000Block110Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4574
    = surrogateDiagTailX0RatChunk000Sub000Block110Part001

theorem surrogateDiagonalTailChunk000Sub000Block110Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part001] using hcert

def TailChunk000Sub000Block110Part002SupportExplicit : Finset ℕ :=
  ([4577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part002 : ℚ :=
  (312951732475 : ℚ) / 225070383994343712

def SurrogateDiagonalTailChunk000Sub000Block110Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4577
    = surrogateDiagTailX0RatChunk000Sub000Block110Part002

theorem surrogateDiagonalTailChunk000Sub000Block110Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part002] using hcert

def TailChunk000Sub000Block110Part003SupportExplicit : Finset ℕ :=
  ([4578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part003 : ℚ :=
  (376311036175 : ℚ) / 7054185323593728

def SurrogateDiagonalTailChunk000Sub000Block110Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4578
    = surrogateDiagTailX0RatChunk000Sub000Block110Part003

theorem surrogateDiagonalTailChunk000Sub000Block110Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part003] using hcert

def TailChunk000Sub000Block110Part004SupportExplicit : Finset ℕ :=
  ([4579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part004 : ℚ :=
  (49769852761 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block110Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4579
    = surrogateDiagTailX0RatChunk000Sub000Block110Part004

theorem surrogateDiagonalTailChunk000Sub000Block110Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part004] using hcert

def TailChunk000Sub000Block110Part005SupportExplicit : Finset ℕ :=
  ([4582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part005 : ℚ :=
  (78522379625 : ℚ) / 7111273926871296

def SurrogateDiagonalTailChunk000Sub000Block110Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4582
    = surrogateDiagTailX0RatChunk000Sub000Block110Part005

theorem surrogateDiagonalTailChunk000Sub000Block110Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part005] using hcert

def TailChunk000Sub000Block110Part006SupportExplicit : Finset ℕ :=
  ([4583] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part006 : ℚ :=
  (328185765625 : ℚ) / 275541619702089522

def SurrogateDiagonalTailChunk000Sub000Block110Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4583
    = surrogateDiagTailX0RatChunk000Sub000Block110Part006

theorem surrogateDiagonalTailChunk000Sub000Block110Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part006] using hcert

def TailChunk000Sub000Block110Part007SupportExplicit : Finset ℕ :=
  ([4585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part007 : ℚ :=
  (3991327991 : ℚ) / 1053083278540800

def SurrogateDiagonalTailChunk000Sub000Block110Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4585
    = surrogateDiagTailX0RatChunk000Sub000Block110Part007

theorem surrogateDiagonalTailChunk000Sub000Block110Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part007] using hcert

def TailChunk000Sub000Block110Part008SupportExplicit : Finset ℕ :=
  ([4586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part008 : ℚ :=
  (657099678775 : ℚ) / 69005755025566848

def SurrogateDiagonalTailChunk000Sub000Block110Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4586
    = surrogateDiagTailX0RatChunk000Sub000Block110Part008

theorem surrogateDiagonalTailChunk000Sub000Block110Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part008] using hcert

def TailChunk000Sub000Block110Part009SupportExplicit : Finset ℕ :=
  ([4587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part009 : ℚ :=
  (15981731927 : ℚ) / 2901971766297600

def SurrogateDiagonalTailChunk000Sub000Block110Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4587
    = surrogateDiagTailX0RatChunk000Sub000Block110Part009

theorem surrogateDiagonalTailChunk000Sub000Block110Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part009] using hcert

def TailChunk000Sub000Block110Part010SupportExplicit : Finset ℕ :=
  ([4589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part010 : ℚ :=
  (1163588132075 : ℚ) / 398008641329823744

def SurrogateDiagonalTailChunk000Sub000Block110Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4589
    = surrogateDiagTailX0RatChunk000Sub000Block110Part010

theorem surrogateDiagonalTailChunk000Sub000Block110Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part010] using hcert

def TailChunk000Sub000Block110Part011SupportExplicit : Finset ℕ :=
  ([4591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part011 : ℚ :=
  (526932025 : ℚ) / 443953610577522

def SurrogateDiagonalTailChunk000Sub000Block110Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4591
    = surrogateDiagTailX0RatChunk000Sub000Block110Part011

theorem surrogateDiagonalTailChunk000Sub000Block110Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part011] using hcert

def TailChunk000Sub000Block110Part012SupportExplicit : Finset ℕ :=
  ([4593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part012 : ℚ :=
  (68899 : ℚ) / 17191569600

def SurrogateDiagonalTailChunk000Sub000Block110Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4593
    = surrogateDiagTailX0RatChunk000Sub000Block110Part012

theorem surrogateDiagonalTailChunk000Sub000Block110Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part012] using hcert

def TailChunk000Sub000Block110Part013SupportExplicit : Finset ℕ :=
  ([4594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part013 : ℚ :=
  (659394219775 : ℚ) / 69488733096265728

def SurrogateDiagonalTailChunk000Sub000Block110Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4594
    = surrogateDiagTailX0RatChunk000Sub000Block110Part013

theorem surrogateDiagonalTailChunk000Sub000Block110Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part013] using hcert

def TailChunk000Sub000Block110Part014SupportExplicit : Finset ℕ :=
  ([4595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part014 : ℚ :=
  (527432840375 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub000Block110Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4595
    = surrogateDiagTailX0RatChunk000Sub000Block110Part014

theorem surrogateDiagonalTailChunk000Sub000Block110Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part014] using hcert

def TailChunk000Sub000Block110Part015SupportExplicit : Finset ℕ :=
  ([4597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part015 : ℚ :=
  (330193890625 : ℚ) / 278924682645932832

def SurrogateDiagonalTailChunk000Sub000Block110Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4597
    = surrogateDiagTailX0RatChunk000Sub000Block110Part015

theorem surrogateDiagonalTailChunk000Sub000Block110Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part015] using hcert

def TailChunk000Sub000Block110Part016SupportExplicit : Finset ℕ :=
  ([4601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part016 : ℚ :=
  (1284418085725 : ℚ) / 982307548856366208

def SurrogateDiagonalTailChunk000Sub000Block110Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4601
    = surrogateDiagTailX0RatChunk000Sub000Block110Part016

theorem surrogateDiagonalTailChunk000Sub000Block110Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part016] using hcert

def TailChunk000Sub000Block110Part017SupportExplicit : Finset ℕ :=
  ([4602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part017 : ℚ :=
  (434466247975 : ℚ) / 9388231713128448

def SurrogateDiagonalTailChunk000Sub000Block110Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4602
    = surrogateDiagTailX0RatChunk000Sub000Block110Part017

theorem surrogateDiagonalTailChunk000Sub000Block110Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part017] using hcert

def TailChunk000Sub000Block110Part018SupportExplicit : Finset ℕ :=
  ([4603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part018 : ℚ :=
  (331056390625 : ℚ) / 280384063091508402

def SurrogateDiagonalTailChunk000Sub000Block110Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4603
    = surrogateDiagTailX0RatChunk000Sub000Block110Part018

theorem surrogateDiagonalTailChunk000Sub000Block110Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part018] using hcert

def TailChunk000Sub000Block110Part019SupportExplicit : Finset ℕ :=
  ([4605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part019 : ℚ :=
  (728312449075 : ℚ) / 89799209329655808

def SurrogateDiagonalTailChunk000Sub000Block110Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4605
    = surrogateDiagTailX0RatChunk000Sub000Block110Part019

theorem surrogateDiagonalTailChunk000Sub000Block110Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part019] using hcert

def TailChunk000Sub000Block110Part020SupportExplicit : Finset ℕ :=
  ([4607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part020 : ℚ :=
  (49963449787 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub000Block110Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4607
    = surrogateDiagTailX0RatChunk000Sub000Block110Part020

theorem surrogateDiagonalTailChunk000Sub000Block110Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part020] using hcert

def TailChunk000Sub000Block110Part021SupportExplicit : Finset ℕ :=
  ([4609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part021 : ℚ :=
  (3241358679 : ℚ) / 2035638791415680

def SurrogateDiagonalTailChunk000Sub000Block110Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4609
    = surrogateDiagTailX0RatChunk000Sub000Block110Part021

theorem surrogateDiagonalTailChunk000Sub000Block110Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part021] using hcert

def TailChunk000Sub000Block110Part022SupportExplicit : Finset ℕ :=
  ([4610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part022 : ℚ :=
  (1483907099 : ℚ) / 57322899087360

def SurrogateDiagonalTailChunk000Sub000Block110Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4610
    = surrogateDiagTailX0RatChunk000Sub000Block110Part022

theorem surrogateDiagonalTailChunk000Sub000Block110Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part022] using hcert

def TailChunk000Sub000Block110Part023SupportExplicit : Finset ℕ :=
  ([4611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part023 : ℚ :=
  (281171595675 : ℚ) / 59933699597664256

def SurrogateDiagonalTailChunk000Sub000Block110Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4611
    = surrogateDiagTailX0RatChunk000Sub000Block110Part023

theorem surrogateDiagonalTailChunk000Sub000Block110Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part023] using hcert

def TailChunk000Sub000Block110Part024SupportExplicit : Finset ℕ :=
  ([4613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block110Part024 : ℚ :=
  (291422553325 : ℚ) / 151871206657457952

def SurrogateDiagonalTailChunk000Sub000Block110Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4613
    = surrogateDiagTailX0RatChunk000Sub000Block110Part024

theorem surrogateDiagonalTailChunk000Sub000Block110Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block110Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block110Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block110Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block110Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block110Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block110HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block110Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block110Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block110Part000
    + surrogateDiagTailX0RatChunk000Sub000Block110Part001
    + surrogateDiagTailX0RatChunk000Sub000Block110Part002
    + surrogateDiagTailX0RatChunk000Sub000Block110Part003
    + surrogateDiagTailX0RatChunk000Sub000Block110Part004
    + surrogateDiagTailX0RatChunk000Sub000Block110Part005
    + surrogateDiagTailX0RatChunk000Sub000Block110Part006
    + surrogateDiagTailX0RatChunk000Sub000Block110Part007
    + surrogateDiagTailX0RatChunk000Sub000Block110Part008
    + surrogateDiagTailX0RatChunk000Sub000Block110Part009

def surrogateDiagonalTailChunk000Sub000Block110MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block110Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block110Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block110Part010
    + surrogateDiagTailX0RatChunk000Sub000Block110Part011
    + surrogateDiagTailX0RatChunk000Sub000Block110Part012
    + surrogateDiagTailX0RatChunk000Sub000Block110Part013
    + surrogateDiagTailX0RatChunk000Sub000Block110Part014
    + surrogateDiagTailX0RatChunk000Sub000Block110Part015
    + surrogateDiagTailX0RatChunk000Sub000Block110Part016
    + surrogateDiagTailX0RatChunk000Sub000Block110Part017
    + surrogateDiagTailX0RatChunk000Sub000Block110Part018
    + surrogateDiagTailX0RatChunk000Sub000Block110Part019

def surrogateDiagonalTailChunk000Sub000Block110TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block110Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block110Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block110Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block110Part020
    + surrogateDiagTailX0RatChunk000Sub000Block110Part021
    + surrogateDiagTailX0RatChunk000Sub000Block110Part022
    + surrogateDiagTailX0RatChunk000Sub000Block110Part023
    + surrogateDiagTailX0RatChunk000Sub000Block110Part024

def surrogateDiagonalTailChunk000Sub000Block110Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block110HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block110MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block110TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block110 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block110Part000
    + surrogateDiagTailX0RatChunk000Sub000Block110Part001
    + surrogateDiagTailX0RatChunk000Sub000Block110Part002
    + surrogateDiagTailX0RatChunk000Sub000Block110Part003
    + surrogateDiagTailX0RatChunk000Sub000Block110Part004
    + surrogateDiagTailX0RatChunk000Sub000Block110Part005
    + surrogateDiagTailX0RatChunk000Sub000Block110Part006
    + surrogateDiagTailX0RatChunk000Sub000Block110Part007
    + surrogateDiagTailX0RatChunk000Sub000Block110Part008
    + surrogateDiagTailX0RatChunk000Sub000Block110Part009
    + surrogateDiagTailX0RatChunk000Sub000Block110Part010
    + surrogateDiagTailX0RatChunk000Sub000Block110Part011
    + surrogateDiagTailX0RatChunk000Sub000Block110Part012
    + surrogateDiagTailX0RatChunk000Sub000Block110Part013
    + surrogateDiagTailX0RatChunk000Sub000Block110Part014
    + surrogateDiagTailX0RatChunk000Sub000Block110Part015
    + surrogateDiagTailX0RatChunk000Sub000Block110Part016
    + surrogateDiagTailX0RatChunk000Sub000Block110Part017
    + surrogateDiagTailX0RatChunk000Sub000Block110Part018
    + surrogateDiagTailX0RatChunk000Sub000Block110Part019
    + surrogateDiagTailX0RatChunk000Sub000Block110Part020
    + surrogateDiagTailX0RatChunk000Sub000Block110Part021
    + surrogateDiagTailX0RatChunk000Sub000Block110Part022
    + surrogateDiagTailX0RatChunk000Sub000Block110Part023
    + surrogateDiagTailX0RatChunk000Sub000Block110Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block110_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block110Head + surrogateDiagTailX0RatChunk000Sub000Block110Mid + surrogateDiagTailX0RatChunk000Sub000Block110Tail =
      surrogateDiagTailX0RatChunk000Sub000Block110 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block110Head surrogateDiagTailX0RatChunk000Sub000Block110Mid surrogateDiagTailX0RatChunk000Sub000Block110Tail surrogateDiagTailX0RatChunk000Sub000Block110
  ring

def SurrogateDiagonalTailChunk000Sub000Block110HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block110HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block110Head

def SurrogateDiagonalTailChunk000Sub000Block110MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block110MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block110Mid

def SurrogateDiagonalTailChunk000Sub000Block110TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block110TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block110Tail

theorem surrogateDiagonalTailChunk000Sub000Block110_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block110HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block110MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block110TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block110Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block110 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block110HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block110MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block110TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block110Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block110_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
