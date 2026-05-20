import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [86,87). -/

/- Block 086 covers tail-support indices [2150,2175) and q from 3585 to 3622. -/

def TailChunk000Sub000Block086Part000SupportExplicit : Finset ℕ :=
  ([3585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part000 : ℚ :=
  (129861506575 : ℚ) / 8215512178040832

def SurrogateDiagonalTailChunk000Sub000Block086Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3585
    = surrogateDiagTailX0RatChunk000Sub000Block086Part000

theorem surrogateDiagonalTailChunk000Sub000Block086Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part000] using hcert

def TailChunk000Sub000Block086Part001SupportExplicit : Finset ℕ :=
  ([3586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part001 : ℚ :=
  (21648652033 : ℚ) / 688885285507200

def SurrogateDiagonalTailChunk000Sub000Block086Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3586
    = surrogateDiagTailX0RatChunk000Sub000Block086Part001

theorem surrogateDiagonalTailChunk000Sub000Block086Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part001] using hcert

def TailChunk000Sub000Block086Part002SupportExplicit : Finset ℕ :=
  ([3587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part002 : ℚ :=
  (15482042729 : ℚ) / 6374027958681600

def SurrogateDiagonalTailChunk000Sub000Block086Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3587
    = surrogateDiagTailX0RatChunk000Sub000Block086Part002

theorem surrogateDiagonalTailChunk000Sub000Block086Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part002] using hcert

def TailChunk000Sub000Block086Part003SupportExplicit : Finset ℕ :=
  ([3589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part003 : ℚ :=
  (29154003625 : ℚ) / 13211679508660224

def SurrogateDiagonalTailChunk000Sub000Block086Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3589
    = surrogateDiagTailX0RatChunk000Sub000Block086Part003

theorem surrogateDiagonalTailChunk000Sub000Block086Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part003] using hcert

def TailChunk000Sub000Block086Part004SupportExplicit : Finset ℕ :=
  ([3590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part004 : ℚ :=
  (3702697325 : ℚ) / 82146480490896

def SurrogateDiagonalTailChunk000Sub000Block086Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3590
    = surrogateDiagTailX0RatChunk000Sub000Block086Part004

theorem surrogateDiagonalTailChunk000Sub000Block086Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part004] using hcert

def TailChunk000Sub000Block086Part005SupportExplicit : Finset ℕ :=
  ([3593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part005 : ℚ :=
  (201713265625 : ℚ) / 104066794991718912

def SurrogateDiagonalTailChunk000Sub000Block086Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3593
    = surrogateDiagTailX0RatChunk000Sub000Block086Part005

theorem surrogateDiagonalTailChunk000Sub000Block086Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part005] using hcert

def TailChunk000Sub000Block086Part006SupportExplicit : Finset ℕ :=
  ([3594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part006 : ℚ :=
  (1549725 : ℚ) / 19673941664

def SurrogateDiagonalTailChunk000Sub000Block086Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3594
    = surrogateDiagTailX0RatChunk000Sub000Block086Part006

theorem surrogateDiagonalTailChunk000Sub000Block086Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part006] using hcert

def TailChunk000Sub000Block086Part007SupportExplicit : Finset ℕ :=
  ([3595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part007 : ℚ :=
  (710211151975 : ℚ) / 170123614447945728

def SurrogateDiagonalTailChunk000Sub000Block086Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3595
    = surrogateDiagTailX0RatChunk000Sub000Block086Part007

theorem surrogateDiagonalTailChunk000Sub000Block086Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part007] using hcert

def TailChunk000Sub000Block086Part008SupportExplicit : Finset ℕ :=
  ([3597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part008 : ℚ :=
  (7704657797 : ℚ) / 725739230822400

def SurrogateDiagonalTailChunk000Sub000Block086Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3597
    = surrogateDiagTailX0RatChunk000Sub000Block086Part008

theorem surrogateDiagonalTailChunk000Sub000Block086Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part008] using hcert

def TailChunk000Sub000Block086Part009SupportExplicit : Finset ℕ :=
  ([3598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part009 : ℚ :=
  (509869300525 : ℚ) / 13918477177847808

def SurrogateDiagonalTailChunk000Sub000Block086Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3598
    = surrogateDiagTailX0RatChunk000Sub000Block086Part009

theorem surrogateDiagonalTailChunk000Sub000Block086Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part009] using hcert

def TailChunk000Sub000Block086Part010SupportExplicit : Finset ℕ :=
  ([3599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part010 : ℚ :=
  (30996067931 : ℚ) / 7334556025881600

def SurrogateDiagonalTailChunk000Sub000Block086Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3599
    = surrogateDiagTailX0RatChunk000Sub000Block086Part010

theorem surrogateDiagonalTailChunk000Sub000Block086Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part010] using hcert

def TailChunk000Sub000Block086Part011SupportExplicit : Finset ℕ :=
  ([3601] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part011 : ℚ :=
  (362826888475 : ℚ) / 75219108182433792

def SurrogateDiagonalTailChunk000Sub000Block086Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3601
    = surrogateDiagTailX0RatChunk000Sub000Block086Part011

theorem surrogateDiagonalTailChunk000Sub000Block086Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part011] using hcert

def TailChunk000Sub000Block086Part012SupportExplicit : Finset ℕ :=
  ([3602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part012 : ℚ :=
  (2701919633 : ℚ) / 116663328000000

def SurrogateDiagonalTailChunk000Sub000Block086Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3602
    = surrogateDiagTailX0RatChunk000Sub000Block086Part012

theorem surrogateDiagonalTailChunk000Sub000Block086Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part012] using hcert

def TailChunk000Sub000Block086Part013SupportExplicit : Finset ℕ :=
  ([3603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part013 : ℚ :=
  (18014650097 : ℚ) / 1659211776000000

def SurrogateDiagonalTailChunk000Sub000Block086Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3603
    = surrogateDiagTailX0RatChunk000Sub000Block086Part013

theorem surrogateDiagonalTailChunk000Sub000Block086Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part013] using hcert

def TailChunk000Sub000Block086Part014SupportExplicit : Finset ℕ :=
  ([3605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part014 : ℚ :=
  (489191460275 : ℚ) / 44899604664827904

def SurrogateDiagonalTailChunk000Sub000Block086Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3605
    = surrogateDiagTailX0RatChunk000Sub000Block086Part014

theorem surrogateDiagonalTailChunk000Sub000Block086Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part014] using hcert

def TailChunk000Sub000Block086Part015SupportExplicit : Finset ℕ :=
  ([3606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part015 : ℚ :=
  (16901 : ℚ) / 216000000

def SurrogateDiagonalTailChunk000Sub000Block086Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3606
    = surrogateDiagTailX0RatChunk000Sub000Block086Part015

theorem surrogateDiagonalTailChunk000Sub000Block086Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part015] using hcert

def TailChunk000Sub000Block086Part016SupportExplicit : Finset ℕ :=
  ([3607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part016 : ℚ :=
  (1625980863775 : ℚ) / 422794908252475848

def SurrogateDiagonalTailChunk000Sub000Block086Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3607
    = surrogateDiagTailX0RatChunk000Sub000Block086Part016

theorem surrogateDiagonalTailChunk000Sub000Block086Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part016] using hcert

def TailChunk000Sub000Block086Part017SupportExplicit : Finset ℕ :=
  ([3611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part017 : ℚ :=
  (98784935825 : ℚ) / 43363665790638336

def SurrogateDiagonalTailChunk000Sub000Block086Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3611
    = surrogateDiagTailX0RatChunk000Sub000Block086Part017

theorem surrogateDiagonalTailChunk000Sub000Block086Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part017] using hcert

def TailChunk000Sub000Block086Part018SupportExplicit : Finset ℕ :=
  ([3613] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part018 : ℚ :=
  (203965140625 : ℚ) / 106403970503752992

def SurrogateDiagonalTailChunk000Sub000Block086Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3613
    = surrogateDiagTailX0RatChunk000Sub000Block086Part018

theorem surrogateDiagonalTailChunk000Sub000Block086Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part018] using hcert

def TailChunk000Sub000Block086Part019SupportExplicit : Finset ℕ :=
  ([3614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part019 : ℚ :=
  (557299993525 : ℚ) / 18804777045608448

def SurrogateDiagonalTailChunk000Sub000Block086Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3614
    = surrogateDiagTailX0RatChunk000Sub000Block086Part019

theorem surrogateDiagonalTailChunk000Sub000Block086Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part019] using hcert

def TailChunk000Sub000Block086Part020SupportExplicit : Finset ℕ :=
  ([3615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part020 : ℚ :=
  (3615649 : ℚ) / 209757143040

def SurrogateDiagonalTailChunk000Sub000Block086Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3615
    = surrogateDiagTailX0RatChunk000Sub000Block086Part020

theorem surrogateDiagonalTailChunk000Sub000Block086Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part020] using hcert

def TailChunk000Sub000Block086Part021SupportExplicit : Finset ℕ :=
  ([3617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part021 : ℚ :=
  (204417015625 : ℚ) / 106876089448660992

def SurrogateDiagonalTailChunk000Sub000Block086Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3617
    = surrogateDiagTailX0RatChunk000Sub000Block086Part021

theorem surrogateDiagonalTailChunk000Sub000Block086Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part021] using hcert

def TailChunk000Sub000Block086Part022SupportExplicit : Finset ℕ :=
  ([3619] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part022 : ℚ :=
  (3013816537 : ℚ) / 644882614732800

def SurrogateDiagonalTailChunk000Sub000Block086Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3619
    = surrogateDiagTailX0RatChunk000Sub000Block086Part022

theorem surrogateDiagonalTailChunk000Sub000Block086Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part022] using hcert

def TailChunk000Sub000Block086Part023SupportExplicit : Finset ℕ :=
  ([3621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part023 : ℚ :=
  (23968192561 : ℚ) / 2518134502195200

def SurrogateDiagonalTailChunk000Sub000Block086Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3621
    = surrogateDiagTailX0RatChunk000Sub000Block086Part023

theorem surrogateDiagonalTailChunk000Sub000Block086Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part023] using hcert

def TailChunk000Sub000Block086Part024SupportExplicit : Finset ℕ :=
  ([3622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block086Part024 : ℚ :=
  (16395325279 : ℚ) / 1073497777624200

def SurrogateDiagonalTailChunk000Sub000Block086Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 3622
    = surrogateDiagTailX0RatChunk000Sub000Block086Part024

theorem surrogateDiagonalTailChunk000Sub000Block086Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block086Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block086Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block086Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block086Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block086Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block086HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block086Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block086Part000
    + surrogateDiagTailX0RatChunk000Sub000Block086Part001
    + surrogateDiagTailX0RatChunk000Sub000Block086Part002
    + surrogateDiagTailX0RatChunk000Sub000Block086Part003
    + surrogateDiagTailX0RatChunk000Sub000Block086Part004
    + surrogateDiagTailX0RatChunk000Sub000Block086Part005
    + surrogateDiagTailX0RatChunk000Sub000Block086Part006
    + surrogateDiagTailX0RatChunk000Sub000Block086Part007
    + surrogateDiagTailX0RatChunk000Sub000Block086Part008
    + surrogateDiagTailX0RatChunk000Sub000Block086Part009

def surrogateDiagonalTailChunk000Sub000Block086MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block086Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block086Part010
    + surrogateDiagTailX0RatChunk000Sub000Block086Part011
    + surrogateDiagTailX0RatChunk000Sub000Block086Part012
    + surrogateDiagTailX0RatChunk000Sub000Block086Part013
    + surrogateDiagTailX0RatChunk000Sub000Block086Part014
    + surrogateDiagTailX0RatChunk000Sub000Block086Part015
    + surrogateDiagTailX0RatChunk000Sub000Block086Part016
    + surrogateDiagTailX0RatChunk000Sub000Block086Part017
    + surrogateDiagTailX0RatChunk000Sub000Block086Part018
    + surrogateDiagTailX0RatChunk000Sub000Block086Part019

def surrogateDiagonalTailChunk000Sub000Block086TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block086Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block086Part020
    + surrogateDiagTailX0RatChunk000Sub000Block086Part021
    + surrogateDiagTailX0RatChunk000Sub000Block086Part022
    + surrogateDiagTailX0RatChunk000Sub000Block086Part023
    + surrogateDiagTailX0RatChunk000Sub000Block086Part024

def surrogateDiagonalTailChunk000Sub000Block086Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block086HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block086MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block086TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block086 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block086Part000
    + surrogateDiagTailX0RatChunk000Sub000Block086Part001
    + surrogateDiagTailX0RatChunk000Sub000Block086Part002
    + surrogateDiagTailX0RatChunk000Sub000Block086Part003
    + surrogateDiagTailX0RatChunk000Sub000Block086Part004
    + surrogateDiagTailX0RatChunk000Sub000Block086Part005
    + surrogateDiagTailX0RatChunk000Sub000Block086Part006
    + surrogateDiagTailX0RatChunk000Sub000Block086Part007
    + surrogateDiagTailX0RatChunk000Sub000Block086Part008
    + surrogateDiagTailX0RatChunk000Sub000Block086Part009
    + surrogateDiagTailX0RatChunk000Sub000Block086Part010
    + surrogateDiagTailX0RatChunk000Sub000Block086Part011
    + surrogateDiagTailX0RatChunk000Sub000Block086Part012
    + surrogateDiagTailX0RatChunk000Sub000Block086Part013
    + surrogateDiagTailX0RatChunk000Sub000Block086Part014
    + surrogateDiagTailX0RatChunk000Sub000Block086Part015
    + surrogateDiagTailX0RatChunk000Sub000Block086Part016
    + surrogateDiagTailX0RatChunk000Sub000Block086Part017
    + surrogateDiagTailX0RatChunk000Sub000Block086Part018
    + surrogateDiagTailX0RatChunk000Sub000Block086Part019
    + surrogateDiagTailX0RatChunk000Sub000Block086Part020
    + surrogateDiagTailX0RatChunk000Sub000Block086Part021
    + surrogateDiagTailX0RatChunk000Sub000Block086Part022
    + surrogateDiagTailX0RatChunk000Sub000Block086Part023
    + surrogateDiagTailX0RatChunk000Sub000Block086Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block086_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block086Head + surrogateDiagTailX0RatChunk000Sub000Block086Mid + surrogateDiagTailX0RatChunk000Sub000Block086Tail =
      surrogateDiagTailX0RatChunk000Sub000Block086 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block086Head surrogateDiagTailX0RatChunk000Sub000Block086Mid surrogateDiagTailX0RatChunk000Sub000Block086Tail surrogateDiagTailX0RatChunk000Sub000Block086
  ring

def SurrogateDiagonalTailChunk000Sub000Block086HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block086HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block086Head

def SurrogateDiagonalTailChunk000Sub000Block086MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block086MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block086Mid

def SurrogateDiagonalTailChunk000Sub000Block086TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block086TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block086Tail

theorem surrogateDiagonalTailChunk000Sub000Block086_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block086HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block086MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block086TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block086Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block086 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block086HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block086MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block086TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block086Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block086_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
