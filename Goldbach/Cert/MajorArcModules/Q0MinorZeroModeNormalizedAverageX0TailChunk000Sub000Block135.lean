import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [135,136). -/

/- Block 135 covers tail-support indices [3375,3400) and q from 5609 to 5647. -/

def TailChunk000Sub000Block135Part000SupportExplicit : Finset ℕ :=
  ([5609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part000 : ℚ :=
  (706893413 : ℚ) / 823064111906400

def SurrogateDiagonalTailChunk000Sub000Block135Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5609
    = surrogateDiagTailX0RatChunk000Sub000Block135Part000

theorem surrogateDiagonalTailChunk000Sub000Block135Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part000] using hcert

def TailChunk000Sub000Block135Part001SupportExplicit : Finset ℕ :=
  ([5610] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part001 : ℚ :=
  (1728200779 : ℚ) / 26848914309120

def SurrogateDiagonalTailChunk000Sub000Block135Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5610
    = surrogateDiagTailX0RatChunk000Sub000Block135Part001

theorem surrogateDiagonalTailChunk000Sub000Block135Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part001] using hcert

def TailChunk000Sub000Block135Part002SupportExplicit : Finset ℕ :=
  ([5611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part002 : ℚ :=
  (37736985701 : ℚ) / 42523783056000000

def SurrogateDiagonalTailChunk000Sub000Block135Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5611
    = surrogateDiagTailX0RatChunk000Sub000Block135Part002

theorem surrogateDiagonalTailChunk000Sub000Block135Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part002] using hcert

def TailChunk000Sub000Block135Part003SupportExplicit : Finset ℕ :=
  ([5613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part003 : ℚ :=
  (8753000309 : ℚ) / 9784604217537600

def SurrogateDiagonalTailChunk000Sub000Block135Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5613
    = surrogateDiagTailX0RatChunk000Sub000Block135Part003

theorem surrogateDiagonalTailChunk000Sub000Block135Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part003] using hcert

def TailChunk000Sub000Block135Part004SupportExplicit : Finset ℕ :=
  ([5614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part004 : ℚ :=
  (2141758363 : ℚ) / 368713728000000

def SurrogateDiagonalTailChunk000Sub000Block135Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5614
    = surrogateDiagTailX0RatChunk000Sub000Block135Part004

theorem surrogateDiagonalTailChunk000Sub000Block135Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part004] using hcert

def TailChunk000Sub000Block135Part005SupportExplicit : Finset ℕ :=
  ([5615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part005 : ℚ :=
  (157891134575 : ℚ) / 507233882637149184

def SurrogateDiagonalTailChunk000Sub000Block135Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5615
    = surrogateDiagTailX0RatChunk000Sub000Block135Part005

theorem surrogateDiagonalTailChunk000Sub000Block135Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part005] using hcert

def TailChunk000Sub000Block135Part006SupportExplicit : Finset ℕ :=
  ([5617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part006 : ℚ :=
  (732858249 : ℚ) / 29198543906406400

def SurrogateDiagonalTailChunk000Sub000Block135Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5617
    = surrogateDiagTailX0RatChunk000Sub000Block135Part006

theorem surrogateDiagonalTailChunk000Sub000Block135Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part006] using hcert

def TailChunk000Sub000Block135Part007SupportExplicit : Finset ℕ :=
  ([5619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part007 : ℚ :=
  (43825625 : ℚ) / 16374276292608

def SurrogateDiagonalTailChunk000Sub000Block135Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5619
    = surrogateDiagTailX0RatChunk000Sub000Block135Part007

theorem surrogateDiagonalTailChunk000Sub000Block135Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part007] using hcert

def TailChunk000Sub000Block135Part008SupportExplicit : Finset ℕ :=
  ([5621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part008 : ℚ :=
  (9795486403 : ℚ) / 5805913846579200

def SurrogateDiagonalTailChunk000Sub000Block135Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5621
    = surrogateDiagTailX0RatChunk000Sub000Block135Part008

theorem surrogateDiagonalTailChunk000Sub000Block135Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part008] using hcert

def TailChunk000Sub000Block135Part009SupportExplicit : Finset ℕ :=
  ([5622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part009 : ℚ :=
  (603050050975 : ℚ) / 30707908402249728

def SurrogateDiagonalTailChunk000Sub000Block135Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5622
    = surrogateDiagTailX0RatChunk000Sub000Block135Part009

theorem surrogateDiagonalTailChunk000Sub000Block135Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part009] using hcert

def TailChunk000Sub000Block135Part010SupportExplicit : Finset ℕ :=
  ([5623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part010 : ℚ :=
  (494033265625 : ℚ) / 624496822007933682

def SurrogateDiagonalTailChunk000Sub000Block135Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5623
    = surrogateDiagTailX0RatChunk000Sub000Block135Part010

theorem surrogateDiagonalTailChunk000Sub000Block135Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part010] using hcert

def TailChunk000Sub000Block135Part011SupportExplicit : Finset ℕ :=
  ([5626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part011 : ℚ :=
  (940780381525 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block135Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5626
    = surrogateDiagTailX0RatChunk000Sub000Block135Part011

theorem surrogateDiagonalTailChunk000Sub000Block135Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part011] using hcert

def TailChunk000Sub000Block135Part012SupportExplicit : Finset ℕ :=
  ([5627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part012 : ℚ :=
  (36860636369 : ℚ) / 38868031379865600

def SurrogateDiagonalTailChunk000Sub000Block135Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5627
    = surrogateDiagTailX0RatChunk000Sub000Block135Part012

theorem surrogateDiagonalTailChunk000Sub000Block135Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part012] using hcert

def TailChunk000Sub000Block135Part013SupportExplicit : Finset ℕ :=
  ([5629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part013 : ℚ :=
  (3728444125 : ℚ) / 3715784861810688

def SurrogateDiagonalTailChunk000Sub000Block135Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5629
    = surrogateDiagTailX0RatChunk000Sub000Block135Part013

theorem surrogateDiagonalTailChunk000Sub000Block135Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part013] using hcert

def TailChunk000Sub000Block135Part014SupportExplicit : Finset ℕ :=
  ([5630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part014 : ℚ :=
  (250504221525 : ℚ) / 21285841882126336

def SurrogateDiagonalTailChunk000Sub000Block135Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5630
    = surrogateDiagTailX0RatChunk000Sub000Block135Part014

theorem surrogateDiagonalTailChunk000Sub000Block135Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part014] using hcert

def TailChunk000Sub000Block135Part015SupportExplicit : Finset ℕ :=
  ([5631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part015 : ℚ :=
  (2694675 : ℚ) / 1011102647296

def SurrogateDiagonalTailChunk000Sub000Block135Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5631
    = surrogateDiagTailX0RatChunk000Sub000Block135Part015

theorem surrogateDiagonalTailChunk000Sub000Block135Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part015] using hcert

def TailChunk000Sub000Block135Part016SupportExplicit : Finset ℕ :=
  ([5633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part016 : ℚ :=
  (76631055373 : ℚ) / 88890924085891200

def SurrogateDiagonalTailChunk000Sub000Block135Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5633
    = surrogateDiagTailX0RatChunk000Sub000Block135Part016

theorem surrogateDiagonalTailChunk000Sub000Block135Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part016] using hcert

def TailChunk000Sub000Block135Part017SupportExplicit : Finset ℕ :=
  ([5637] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part017 : ℚ :=
  (275738121175 : ℚ) / 124413985316058912

def SurrogateDiagonalTailChunk000Sub000Block135Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5637
    = surrogateDiagTailX0RatChunk000Sub000Block135Part017

theorem surrogateDiagonalTailChunk000Sub000Block135Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part017] using hcert

def TailChunk000Sub000Block135Part018SupportExplicit : Finset ℕ :=
  ([5638] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part018 : ℚ :=
  (993146455975 : ℚ) / 157685156683631688

def SurrogateDiagonalTailChunk000Sub000Block135Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5638
    = surrogateDiagTailX0RatChunk000Sub000Block135Part018

theorem surrogateDiagonalTailChunk000Sub000Block135Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part018] using hcert

def TailChunk000Sub000Block135Part019SupportExplicit : Finset ℕ :=
  ([5639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part019 : ℚ :=
  (496848765625 : ℚ) / 631636405931992242

def SurrogateDiagonalTailChunk000Sub000Block135Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5639
    = surrogateDiagTailX0RatChunk000Sub000Block135Part019

theorem surrogateDiagonalTailChunk000Sub000Block135Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part019] using hcert

def TailChunk000Sub000Block135Part020SupportExplicit : Finset ℕ :=
  ([5641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part020 : ℚ :=
  (795522025 : ℚ) / 1012053022290432

def SurrogateDiagonalTailChunk000Sub000Block135Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5641
    = surrogateDiagTailX0RatChunk000Sub000Block135Part020

theorem surrogateDiagonalTailChunk000Sub000Block135Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part020] using hcert

def TailChunk000Sub000Block135Part021SupportExplicit : Finset ℕ :=
  ([5642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part021 : ℚ :=
  (29753334493 : ℚ) / 2177217692467200

def SurrogateDiagonalTailChunk000Sub000Block135Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5642
    = surrogateDiagTailX0RatChunk000Sub000Block135Part021

theorem surrogateDiagonalTailChunk000Sub000Block135Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part021] using hcert

def TailChunk000Sub000Block135Part022SupportExplicit : Finset ℕ :=
  ([5645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part022 : ℚ :=
  (796024047875 : ℚ) / 518171147412701184

def SurrogateDiagonalTailChunk000Sub000Block135Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5645
    = surrogateDiagTailX0RatChunk000Sub000Block135Part022

theorem surrogateDiagonalTailChunk000Sub000Block135Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part022] using hcert

def TailChunk000Sub000Block135Part023SupportExplicit : Finset ℕ :=
  ([5646] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part023 : ℚ :=
  (3539750687 : ℚ) / 249889635133440

def SurrogateDiagonalTailChunk000Sub000Block135Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5646
    = surrogateDiagTailX0RatChunk000Sub000Block135Part023

theorem surrogateDiagonalTailChunk000Sub000Block135Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part023] using hcert

def TailChunk000Sub000Block135Part024SupportExplicit : Finset ℕ :=
  ([5647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block135Part024 : ℚ :=
  (498259515625 : ℚ) / 635229067511830482

def SurrogateDiagonalTailChunk000Sub000Block135Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5647
    = surrogateDiagTailX0RatChunk000Sub000Block135Part024

theorem surrogateDiagonalTailChunk000Sub000Block135Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block135Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block135Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block135Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block135Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block135Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block135Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block135HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block135Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block135Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block135Part000
    + surrogateDiagTailX0RatChunk000Sub000Block135Part001
    + surrogateDiagTailX0RatChunk000Sub000Block135Part002
    + surrogateDiagTailX0RatChunk000Sub000Block135Part003
    + surrogateDiagTailX0RatChunk000Sub000Block135Part004
    + surrogateDiagTailX0RatChunk000Sub000Block135Part005
    + surrogateDiagTailX0RatChunk000Sub000Block135Part006
    + surrogateDiagTailX0RatChunk000Sub000Block135Part007
    + surrogateDiagTailX0RatChunk000Sub000Block135Part008
    + surrogateDiagTailX0RatChunk000Sub000Block135Part009

def surrogateDiagonalTailChunk000Sub000Block135MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block135Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block135Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block135Part010
    + surrogateDiagTailX0RatChunk000Sub000Block135Part011
    + surrogateDiagTailX0RatChunk000Sub000Block135Part012
    + surrogateDiagTailX0RatChunk000Sub000Block135Part013
    + surrogateDiagTailX0RatChunk000Sub000Block135Part014
    + surrogateDiagTailX0RatChunk000Sub000Block135Part015
    + surrogateDiagTailX0RatChunk000Sub000Block135Part016
    + surrogateDiagTailX0RatChunk000Sub000Block135Part017
    + surrogateDiagTailX0RatChunk000Sub000Block135Part018
    + surrogateDiagTailX0RatChunk000Sub000Block135Part019

def surrogateDiagonalTailChunk000Sub000Block135TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block135Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block135Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block135Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block135Part020
    + surrogateDiagTailX0RatChunk000Sub000Block135Part021
    + surrogateDiagTailX0RatChunk000Sub000Block135Part022
    + surrogateDiagTailX0RatChunk000Sub000Block135Part023
    + surrogateDiagTailX0RatChunk000Sub000Block135Part024

def surrogateDiagonalTailChunk000Sub000Block135Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block135HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block135MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block135TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block135 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block135Part000
    + surrogateDiagTailX0RatChunk000Sub000Block135Part001
    + surrogateDiagTailX0RatChunk000Sub000Block135Part002
    + surrogateDiagTailX0RatChunk000Sub000Block135Part003
    + surrogateDiagTailX0RatChunk000Sub000Block135Part004
    + surrogateDiagTailX0RatChunk000Sub000Block135Part005
    + surrogateDiagTailX0RatChunk000Sub000Block135Part006
    + surrogateDiagTailX0RatChunk000Sub000Block135Part007
    + surrogateDiagTailX0RatChunk000Sub000Block135Part008
    + surrogateDiagTailX0RatChunk000Sub000Block135Part009
    + surrogateDiagTailX0RatChunk000Sub000Block135Part010
    + surrogateDiagTailX0RatChunk000Sub000Block135Part011
    + surrogateDiagTailX0RatChunk000Sub000Block135Part012
    + surrogateDiagTailX0RatChunk000Sub000Block135Part013
    + surrogateDiagTailX0RatChunk000Sub000Block135Part014
    + surrogateDiagTailX0RatChunk000Sub000Block135Part015
    + surrogateDiagTailX0RatChunk000Sub000Block135Part016
    + surrogateDiagTailX0RatChunk000Sub000Block135Part017
    + surrogateDiagTailX0RatChunk000Sub000Block135Part018
    + surrogateDiagTailX0RatChunk000Sub000Block135Part019
    + surrogateDiagTailX0RatChunk000Sub000Block135Part020
    + surrogateDiagTailX0RatChunk000Sub000Block135Part021
    + surrogateDiagTailX0RatChunk000Sub000Block135Part022
    + surrogateDiagTailX0RatChunk000Sub000Block135Part023
    + surrogateDiagTailX0RatChunk000Sub000Block135Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block135_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block135Head + surrogateDiagTailX0RatChunk000Sub000Block135Mid + surrogateDiagTailX0RatChunk000Sub000Block135Tail =
      surrogateDiagTailX0RatChunk000Sub000Block135 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block135Head surrogateDiagTailX0RatChunk000Sub000Block135Mid surrogateDiagTailX0RatChunk000Sub000Block135Tail surrogateDiagTailX0RatChunk000Sub000Block135
  ring

def SurrogateDiagonalTailChunk000Sub000Block135HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block135HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block135Head

def SurrogateDiagonalTailChunk000Sub000Block135MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block135MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block135Mid

def SurrogateDiagonalTailChunk000Sub000Block135TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block135TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block135Tail

theorem surrogateDiagonalTailChunk000Sub000Block135_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block135HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block135MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block135TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block135Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block135 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block135HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block135MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block135TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block135Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block135_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
