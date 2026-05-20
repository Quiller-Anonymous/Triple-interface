import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 001, blocks [80,90). -/

/-- Block 080 covers tail-support indices [7000,7025) and q from 11567 to 11605. -/

def TailChunk000Sub001Block080Part000SupportExplicit : Finset ℕ :=
  ([11567] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part000 : ℚ :=
  (49091818925 : ℚ) / 20069345101996237824

def SurrogateDiagonalTailChunk000Sub001Block080Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11567
    = surrogateDiagTailX0RatChunk000Sub001Block080Part000

theorem surrogateDiagonalTailChunk000Sub001Block080Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part000] using hcert

def TailChunk000Sub001Block080Part001SupportExplicit : Finset ℕ :=
  ([11569] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part001 : ℚ :=
  (148389619375 : ℚ) / 37199101552254162048

def SurrogateDiagonalTailChunk000Sub001Block080Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11569
    = surrogateDiagTailX0RatChunk000Sub001Block080Part001

theorem surrogateDiagonalTailChunk000Sub001Block080Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part001] using hcert

def TailChunk000Sub001Block080Part002SupportExplicit : Finset ℕ :=
  ([11570] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part002 : ℚ :=
  (89848257025 : ℚ) / 49751080166227968

def SurrogateDiagonalTailChunk000Sub001Block080Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11570
    = surrogateDiagTailX0RatChunk000Sub001Block080Part002

theorem surrogateDiagonalTailChunk000Sub001Block080Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part002] using hcert

def TailChunk000Sub001Block080Part003SupportExplicit : Finset ℕ :=
  ([11571] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part003 : ℚ :=
  (1002754636225 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub001Block080Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11571
    = surrogateDiagTailX0RatChunk000Sub001Block080Part003

theorem surrogateDiagonalTailChunk000Sub001Block080Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part003] using hcert

def TailChunk000Sub001Block080Part004SupportExplicit : Finset ℕ :=
  ([11573] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part004 : ℚ :=
  (13769669 : ℚ) / 7876255097632320

def SurrogateDiagonalTailChunk000Sub001Block080Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11573
    = surrogateDiagTailX0RatChunk000Sub001Block080Part004

theorem surrogateDiagonalTailChunk000Sub001Block080Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part004] using hcert

def TailChunk000Sub001Block080Part005SupportExplicit : Finset ℕ :=
  ([11577] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part005 : ℚ :=
  (480647805425 : ℚ) / 3420034862357151744

def SurrogateDiagonalTailChunk000Sub001Block080Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11577
    = surrogateDiagTailX0RatChunk000Sub001Block080Part005

theorem surrogateDiagonalTailChunk000Sub001Block080Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part005] using hcert

def TailChunk000Sub001Block080Part006SupportExplicit : Finset ℕ :=
  ([11578] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part006 : ℚ :=
  (1750545554575 : ℚ) / 1508523394520274048

def SurrogateDiagonalTailChunk000Sub001Block080Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11578
    = surrogateDiagTailX0RatChunk000Sub001Block080Part006

theorem surrogateDiagonalTailChunk000Sub001Block080Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part006] using hcert

def TailChunk000Sub001Block080Part007SupportExplicit : Finset ℕ :=
  ([11579] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part007 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block080Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11579
    = surrogateDiagTailX0RatChunk000Sub001Block080Part007

theorem surrogateDiagonalTailChunk000Sub001Block080Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part007] using hcert

def TailChunk000Sub001Block080Part008SupportExplicit : Finset ℕ :=
  ([11581] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part008 : ℚ :=
  (108291091375 : ℚ) / 39797449289315647488

def SurrogateDiagonalTailChunk000Sub001Block080Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11581
    = surrogateDiagTailX0RatChunk000Sub001Block080Part008

theorem surrogateDiagonalTailChunk000Sub001Block080Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part008] using hcert

def TailChunk000Sub001Block080Part009SupportExplicit : Finset ℕ :=
  ([11582] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part009 : ℚ :=
  (838392025 : ℚ) / 1124090053866162

def SurrogateDiagonalTailChunk000Sub001Block080Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11582
    = surrogateDiagTailX0RatChunk000Sub001Block080Part009

theorem surrogateDiagonalTailChunk000Sub001Block080Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part009] using hcert

def TailChunk000Sub001Block080Part010SupportExplicit : Finset ℕ :=
  ([11585] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part010 : ℚ :=
  (35688765091 : ℚ) / 393538817721139200

def SurrogateDiagonalTailChunk000Sub001Block080Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11585
    = surrogateDiagTailX0RatChunk000Sub001Block080Part010

theorem surrogateDiagonalTailChunk000Sub001Block080Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part010] using hcert

def TailChunk000Sub001Block080Part011SupportExplicit : Finset ℕ :=
  ([11586] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part011 : ℚ :=
  (5589849 : ℚ) / 2219980801600

def SurrogateDiagonalTailChunk000Sub001Block080Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11586
    = surrogateDiagTailX0RatChunk000Sub001Block080Part011

theorem surrogateDiagonalTailChunk000Sub001Block080Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part011] using hcert

def TailChunk000Sub001Block080Part012SupportExplicit : Finset ℕ :=
  ([11587] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part012 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block080Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11587
    = surrogateDiagTailX0RatChunk000Sub001Block080Part012

theorem surrogateDiagonalTailChunk000Sub001Block080Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part012] using hcert

def TailChunk000Sub001Block080Part013SupportExplicit : Finset ℕ :=
  ([11589] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part013 : ℚ :=
  (466407670475 : ℚ) / 4450060584588807744

def SurrogateDiagonalTailChunk000Sub001Block080Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11589
    = surrogateDiagTailX0RatChunk000Sub001Block080Part013

theorem surrogateDiagonalTailChunk000Sub001Block080Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part013] using hcert

def TailChunk000Sub001Block080Part014SupportExplicit : Finset ℕ :=
  ([11590] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part014 : ℚ :=
  (59018015941 : ℚ) / 34835483079475200

def SurrogateDiagonalTailChunk000Sub001Block080Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11590
    = surrogateDiagTailX0RatChunk000Sub001Block080Part014

theorem surrogateDiagonalTailChunk000Sub001Block080Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part014] using hcert

def TailChunk000Sub001Block080Part015SupportExplicit : Finset ℕ :=
  ([11591] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part015 : ℚ :=
  (37021517825 : ℚ) / 20762822585861858304

def SurrogateDiagonalTailChunk000Sub001Block080Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11591
    = surrogateDiagTailX0RatChunk000Sub001Block080Part015

theorem surrogateDiagonalTailChunk000Sub001Block080Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part015] using hcert

def TailChunk000Sub001Block080Part016SupportExplicit : Finset ℕ :=
  ([11593] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block080Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11593
    = surrogateDiagTailX0RatChunk000Sub001Block080Part016

theorem surrogateDiagonalTailChunk000Sub001Block080Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part016] using hcert

def TailChunk000Sub001Block080Part017SupportExplicit : Finset ℕ :=
  ([11594] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part017 : ℚ :=
  (3398803607 : ℚ) / 2654738841600000

def SurrogateDiagonalTailChunk000Sub001Block080Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11594
    = surrogateDiagTailX0RatChunk000Sub001Block080Part017

theorem surrogateDiagonalTailChunk000Sub001Block080Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part017] using hcert

def TailChunk000Sub001Block080Part018SupportExplicit : Finset ℕ :=
  ([11595] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part018 : ℚ :=
  (1045560735025 : ℚ) / 3637943988650508288

def SurrogateDiagonalTailChunk000Sub001Block080Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11595
    = surrogateDiagTailX0RatChunk000Sub001Block080Part018

theorem surrogateDiagonalTailChunk000Sub001Block080Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part018] using hcert

def TailChunk000Sub001Block080Part019SupportExplicit : Finset ℕ :=
  ([11597] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part019 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block080Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11597
    = surrogateDiagTailX0RatChunk000Sub001Block080Part019

theorem surrogateDiagonalTailChunk000Sub001Block080Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part019] using hcert

def TailChunk000Sub001Block080Part020SupportExplicit : Finset ℕ :=
  ([11598] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part020 : ℚ :=
  (952625 : ℚ) / 379115154432

def SurrogateDiagonalTailChunk000Sub001Block080Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11598
    = surrogateDiagTailX0RatChunk000Sub001Block080Part020

theorem surrogateDiagonalTailChunk000Sub001Block080Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part020] using hcert

def TailChunk000Sub001Block080Part021SupportExplicit : Finset ℕ :=
  ([11599] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part021 : ℚ :=
  (9552906475 : ℚ) / 451314649094602752

def SurrogateDiagonalTailChunk000Sub001Block080Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11599
    = surrogateDiagTailX0RatChunk000Sub001Block080Part021

theorem surrogateDiagonalTailChunk000Sub001Block080Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part021] using hcert

def TailChunk000Sub001Block080Part022SupportExplicit : Finset ℕ :=
  ([11602] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part022 : ℚ :=
  (33651601 : ℚ) / 45275037196800

def SurrogateDiagonalTailChunk000Sub001Block080Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11602
    = surrogateDiagTailX0RatChunk000Sub001Block080Part022

theorem surrogateDiagonalTailChunk000Sub001Block080Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part022] using hcert

def TailChunk000Sub001Block080Part023SupportExplicit : Finset ℕ :=
  ([11603] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part023 : ℚ :=
  (2033284367 : ℚ) / 809642417832345600

def SurrogateDiagonalTailChunk000Sub001Block080Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11603
    = surrogateDiagTailX0RatChunk000Sub001Block080Part023

theorem surrogateDiagonalTailChunk000Sub001Block080Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part023] using hcert

def TailChunk000Sub001Block080Part024SupportExplicit : Finset ℕ :=
  ([11605] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block080Part024 : ℚ :=
  (33238889899 : ℚ) / 497970934272000000

def SurrogateDiagonalTailChunk000Sub001Block080Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11605
    = surrogateDiagTailX0RatChunk000Sub001Block080Part024

theorem surrogateDiagonalTailChunk000Sub001Block080Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block080Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block080Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block080Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block080Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block080Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block080HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block080Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block080Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block080Part000
    + surrogateDiagTailX0RatChunk000Sub001Block080Part001
    + surrogateDiagTailX0RatChunk000Sub001Block080Part002
    + surrogateDiagTailX0RatChunk000Sub001Block080Part003
    + surrogateDiagTailX0RatChunk000Sub001Block080Part004
    + surrogateDiagTailX0RatChunk000Sub001Block080Part005
    + surrogateDiagTailX0RatChunk000Sub001Block080Part006
    + surrogateDiagTailX0RatChunk000Sub001Block080Part007
    + surrogateDiagTailX0RatChunk000Sub001Block080Part008
    + surrogateDiagTailX0RatChunk000Sub001Block080Part009

def surrogateDiagonalTailChunk000Sub001Block080MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block080Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block080Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block080Part010
    + surrogateDiagTailX0RatChunk000Sub001Block080Part011
    + surrogateDiagTailX0RatChunk000Sub001Block080Part012
    + surrogateDiagTailX0RatChunk000Sub001Block080Part013
    + surrogateDiagTailX0RatChunk000Sub001Block080Part014
    + surrogateDiagTailX0RatChunk000Sub001Block080Part015
    + surrogateDiagTailX0RatChunk000Sub001Block080Part016
    + surrogateDiagTailX0RatChunk000Sub001Block080Part017
    + surrogateDiagTailX0RatChunk000Sub001Block080Part018
    + surrogateDiagTailX0RatChunk000Sub001Block080Part019

def surrogateDiagonalTailChunk000Sub001Block080TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block080Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block080Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block080Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block080Part020
    + surrogateDiagTailX0RatChunk000Sub001Block080Part021
    + surrogateDiagTailX0RatChunk000Sub001Block080Part022
    + surrogateDiagTailX0RatChunk000Sub001Block080Part023
    + surrogateDiagTailX0RatChunk000Sub001Block080Part024

def surrogateDiagonalTailChunk000Sub001Block080Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block080HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block080MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block080TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block080 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block080Part000
    + surrogateDiagTailX0RatChunk000Sub001Block080Part001
    + surrogateDiagTailX0RatChunk000Sub001Block080Part002
    + surrogateDiagTailX0RatChunk000Sub001Block080Part003
    + surrogateDiagTailX0RatChunk000Sub001Block080Part004
    + surrogateDiagTailX0RatChunk000Sub001Block080Part005
    + surrogateDiagTailX0RatChunk000Sub001Block080Part006
    + surrogateDiagTailX0RatChunk000Sub001Block080Part007
    + surrogateDiagTailX0RatChunk000Sub001Block080Part008
    + surrogateDiagTailX0RatChunk000Sub001Block080Part009
    + surrogateDiagTailX0RatChunk000Sub001Block080Part010
    + surrogateDiagTailX0RatChunk000Sub001Block080Part011
    + surrogateDiagTailX0RatChunk000Sub001Block080Part012
    + surrogateDiagTailX0RatChunk000Sub001Block080Part013
    + surrogateDiagTailX0RatChunk000Sub001Block080Part014
    + surrogateDiagTailX0RatChunk000Sub001Block080Part015
    + surrogateDiagTailX0RatChunk000Sub001Block080Part016
    + surrogateDiagTailX0RatChunk000Sub001Block080Part017
    + surrogateDiagTailX0RatChunk000Sub001Block080Part018
    + surrogateDiagTailX0RatChunk000Sub001Block080Part019
    + surrogateDiagTailX0RatChunk000Sub001Block080Part020
    + surrogateDiagTailX0RatChunk000Sub001Block080Part021
    + surrogateDiagTailX0RatChunk000Sub001Block080Part022
    + surrogateDiagTailX0RatChunk000Sub001Block080Part023
    + surrogateDiagTailX0RatChunk000Sub001Block080Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block080_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block080Head + surrogateDiagTailX0RatChunk000Sub001Block080Mid + surrogateDiagTailX0RatChunk000Sub001Block080Tail =
      surrogateDiagTailX0RatChunk000Sub001Block080 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block080Head surrogateDiagTailX0RatChunk000Sub001Block080Mid surrogateDiagTailX0RatChunk000Sub001Block080Tail surrogateDiagTailX0RatChunk000Sub001Block080
  ring

def SurrogateDiagonalTailChunk000Sub001Block080HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block080HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block080Head

def SurrogateDiagonalTailChunk000Sub001Block080MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block080MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block080Mid

def SurrogateDiagonalTailChunk000Sub001Block080TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block080TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block080Tail

theorem surrogateDiagonalTailChunk000Sub001Block080_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block080HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block080MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block080TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block080Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block080 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block080HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block080MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block080TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block080Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block080_eq_head_add_mid_add_tail

/-- Block 081 covers tail-support indices [7025,7050) and q from 11606 to 11647. -/

def TailChunk000Sub001Block081Part000SupportExplicit : Finset ℕ :=
  ([11606] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part000 : ℚ :=
  (1759023958375 : ℚ) / 1523186940694284288

def SurrogateDiagonalTailChunk000Sub001Block081Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11606
    = surrogateDiagTailX0RatChunk000Sub001Block081Part000

theorem surrogateDiagonalTailChunk000Sub001Block081Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part000] using hcert

def TailChunk000Sub001Block081Part001SupportExplicit : Finset ℕ :=
  ([11607] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part001 : ℚ :=
  (951915028375 : ℚ) / 7861224550975930368

def SurrogateDiagonalTailChunk000Sub001Block081Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11607
    = surrogateDiagTailX0RatChunk000Sub001Block081Part001

theorem surrogateDiagonalTailChunk000Sub001Block081Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part001] using hcert

def TailChunk000Sub001Block081Part002SupportExplicit : Finset ℕ :=
  ([11609] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part002 : ℚ :=
  (243986032475 : ℚ) / 12185495525554274304

def SurrogateDiagonalTailChunk000Sub001Block081Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11609
    = surrogateDiagTailX0RatChunk000Sub001Block081Part002

theorem surrogateDiagonalTailChunk000Sub001Block081Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part002] using hcert

def TailChunk000Sub001Block081Part003SupportExplicit : Finset ℕ :=
  ([11611] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part003 : ℚ :=
  (104122915925 : ℚ) / 17726144794056720384

def SurrogateDiagonalTailChunk000Sub001Block081Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11611
    = surrogateDiagTailX0RatChunk000Sub001Block081Part003

theorem surrogateDiagonalTailChunk000Sub001Block081Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part003] using hcert

def TailChunk000Sub001Block081Part004SupportExplicit : Finset ℕ :=
  ([11614] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block081Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11614
    = surrogateDiagTailX0RatChunk000Sub001Block081Part004

theorem surrogateDiagonalTailChunk000Sub001Block081Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part004] using hcert

def TailChunk000Sub001Block081Part005SupportExplicit : Finset ℕ :=
  ([11615] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part005 : ℚ :=
  (94534553 : ℚ) / 1874422809600000

def SurrogateDiagonalTailChunk000Sub001Block081Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11615
    = surrogateDiagTailX0RatChunk000Sub001Block081Part005

theorem surrogateDiagonalTailChunk000Sub001Block081Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part005] using hcert

def TailChunk000Sub001Block081Part006SupportExplicit : Finset ℕ :=
  ([11617] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block081Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11617
    = surrogateDiagTailX0RatChunk000Sub001Block081Part006

theorem surrogateDiagonalTailChunk000Sub001Block081Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part006] using hcert

def TailChunk000Sub001Block081Part007SupportExplicit : Finset ℕ :=
  ([11618] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part007 : ℚ :=
  (59606352775 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub001Block081Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11618
    = surrogateDiagTailX0RatChunk000Sub001Block081Part007

theorem surrogateDiagonalTailChunk000Sub001Block081Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part007] using hcert

def TailChunk000Sub001Block081Part008SupportExplicit : Finset ℕ :=
  ([11621] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block081Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11621
    = surrogateDiagTailX0RatChunk000Sub001Block081Part008

theorem surrogateDiagonalTailChunk000Sub001Block081Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part008] using hcert

def TailChunk000Sub001Block081Part009SupportExplicit : Finset ℕ :=
  ([11622] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part009 : ℚ :=
  (61332363725 : ℚ) / 49754080021118976

def SurrogateDiagonalTailChunk000Sub001Block081Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11622
    = surrogateDiagTailX0RatChunk000Sub001Block081Part009

theorem surrogateDiagonalTailChunk000Sub001Block081Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part009] using hcert

def TailChunk000Sub001Block081Part010SupportExplicit : Finset ℕ :=
  ([11623] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part010 : ℚ :=
  (77912656375 : ℚ) / 41760252753143973888

def SurrogateDiagonalTailChunk000Sub001Block081Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11623
    = surrogateDiagTailX0RatChunk000Sub001Block081Part010

theorem surrogateDiagonalTailChunk000Sub001Block081Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part010] using hcert

def TailChunk000Sub001Block081Part011SupportExplicit : Finset ℕ :=
  ([11626] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part011 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block081Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11626
    = surrogateDiagTailX0RatChunk000Sub001Block081Part011

theorem surrogateDiagonalTailChunk000Sub001Block081Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part011] using hcert

def TailChunk000Sub001Block081Part012SupportExplicit : Finset ℕ :=
  ([11627] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part012 : ℚ :=
  (5436692843 : ℚ) / 131246244000000000

def SurrogateDiagonalTailChunk000Sub001Block081Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11627
    = surrogateDiagTailX0RatChunk000Sub001Block081Part012

theorem surrogateDiagonalTailChunk000Sub001Block081Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part012] using hcert

def TailChunk000Sub001Block081Part013SupportExplicit : Finset ℕ :=
  ([11629] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part013 : ℚ :=
  (664146429 : ℚ) / 3278820966400000

def SurrogateDiagonalTailChunk000Sub001Block081Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11629
    = surrogateDiagTailX0RatChunk000Sub001Block081Part013

theorem surrogateDiagonalTailChunk000Sub001Block081Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part013] using hcert

def TailChunk000Sub001Block081Part014SupportExplicit : Finset ℕ :=
  ([11630] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part014 : ℚ :=
  (844696280375 : ℚ) / 583527517218530304

def SurrogateDiagonalTailChunk000Sub001Block081Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11630
    = surrogateDiagTailX0RatChunk000Sub001Block081Part014

theorem surrogateDiagonalTailChunk000Sub001Block081Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part014] using hcert

def TailChunk000Sub001Block081Part015SupportExplicit : Finset ℕ :=
  ([11631] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part015 : ℚ :=
  (2348090504675 : ℚ) / 4514939336053269504

def SurrogateDiagonalTailChunk000Sub001Block081Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11631
    = surrogateDiagTailX0RatChunk000Sub001Block081Part015

theorem surrogateDiagonalTailChunk000Sub001Block081Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part015] using hcert

def TailChunk000Sub001Block081Part016SupportExplicit : Finset ℕ :=
  ([11633] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part016 : ℚ :=
  (2114479515625 : ℚ) / 11444173718395625472

def SurrogateDiagonalTailChunk000Sub001Block081Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11633
    = surrogateDiagTailX0RatChunk000Sub001Block081Part016

theorem surrogateDiagonalTailChunk000Sub001Block081Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part016] using hcert

def TailChunk000Sub001Block081Part017SupportExplicit : Finset ℕ :=
  ([11634] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part017 : ℚ :=
  (19582325 : ℚ) / 5013604491264

def SurrogateDiagonalTailChunk000Sub001Block081Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11634
    = surrogateDiagTailX0RatChunk000Sub001Block081Part017

theorem surrogateDiagonalTailChunk000Sub001Block081Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part017] using hcert

def TailChunk000Sub001Block081Part018SupportExplicit : Finset ℕ :=
  ([11635] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part018 : ℚ :=
  (1336629377725 : ℚ) / 3331285283834560512

def SurrogateDiagonalTailChunk000Sub001Block081Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11635
    = surrogateDiagTailX0RatChunk000Sub001Block081Part018

theorem surrogateDiagonalTailChunk000Sub001Block081Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part018] using hcert

def TailChunk000Sub001Block081Part019SupportExplicit : Finset ℕ :=
  ([11639] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part019 : ℚ :=
  (2055799666525 : ℚ) / 10647303782740918272

def SurrogateDiagonalTailChunk000Sub001Block081Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11639
    = surrogateDiagTailX0RatChunk000Sub001Block081Part019

theorem surrogateDiagonalTailChunk000Sub001Block081Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part019] using hcert

def TailChunk000Sub001Block081Part020SupportExplicit : Finset ℕ :=
  ([11641] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part020 : ℚ :=
  (410185024375 : ℚ) / 1545382377568619208

def SurrogateDiagonalTailChunk000Sub001Block081Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11641
    = surrogateDiagTailX0RatChunk000Sub001Block081Part020

theorem surrogateDiagonalTailChunk000Sub001Block081Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part020] using hcert

def TailChunk000Sub001Block081Part021SupportExplicit : Finset ℕ :=
  ([11642] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part021 : ℚ :=
  (847101025 : ℚ) / 1147568949656352

def SurrogateDiagonalTailChunk000Sub001Block081Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11642
    = surrogateDiagTailX0RatChunk000Sub001Block081Part021

theorem surrogateDiagonalTailChunk000Sub001Block081Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part021] using hcert

def TailChunk000Sub001Block081Part022SupportExplicit : Finset ℕ :=
  ([11643] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part022 : ℚ :=
  (94117551209 : ℚ) / 181344229081497600

def SurrogateDiagonalTailChunk000Sub001Block081Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11643
    = surrogateDiagTailX0RatChunk000Sub001Block081Part022

theorem surrogateDiagonalTailChunk000Sub001Block081Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part022] using hcert

def TailChunk000Sub001Block081Part023SupportExplicit : Finset ℕ :=
  ([11645] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part023 : ℚ :=
  (1303254163225 : ℚ) / 3587917075219218432

def SurrogateDiagonalTailChunk000Sub001Block081Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11645
    = surrogateDiagTailX0RatChunk000Sub001Block081Part023

theorem surrogateDiagonalTailChunk000Sub001Block081Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part023] using hcert

def TailChunk000Sub001Block081Part024SupportExplicit : Finset ℕ :=
  ([11647] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block081Part024 : ℚ :=
  (287220813275 : ℚ) / 1363825491694147584

def SurrogateDiagonalTailChunk000Sub001Block081Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11647
    = surrogateDiagTailX0RatChunk000Sub001Block081Part024

theorem surrogateDiagonalTailChunk000Sub001Block081Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block081Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block081Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block081Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block081Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block081Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block081HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block081Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block081Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block081Part000
    + surrogateDiagTailX0RatChunk000Sub001Block081Part001
    + surrogateDiagTailX0RatChunk000Sub001Block081Part002
    + surrogateDiagTailX0RatChunk000Sub001Block081Part003
    + surrogateDiagTailX0RatChunk000Sub001Block081Part004
    + surrogateDiagTailX0RatChunk000Sub001Block081Part005
    + surrogateDiagTailX0RatChunk000Sub001Block081Part006
    + surrogateDiagTailX0RatChunk000Sub001Block081Part007
    + surrogateDiagTailX0RatChunk000Sub001Block081Part008
    + surrogateDiagTailX0RatChunk000Sub001Block081Part009

def surrogateDiagonalTailChunk000Sub001Block081MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block081Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block081Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block081Part010
    + surrogateDiagTailX0RatChunk000Sub001Block081Part011
    + surrogateDiagTailX0RatChunk000Sub001Block081Part012
    + surrogateDiagTailX0RatChunk000Sub001Block081Part013
    + surrogateDiagTailX0RatChunk000Sub001Block081Part014
    + surrogateDiagTailX0RatChunk000Sub001Block081Part015
    + surrogateDiagTailX0RatChunk000Sub001Block081Part016
    + surrogateDiagTailX0RatChunk000Sub001Block081Part017
    + surrogateDiagTailX0RatChunk000Sub001Block081Part018
    + surrogateDiagTailX0RatChunk000Sub001Block081Part019

def surrogateDiagonalTailChunk000Sub001Block081TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block081Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block081Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block081Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block081Part020
    + surrogateDiagTailX0RatChunk000Sub001Block081Part021
    + surrogateDiagTailX0RatChunk000Sub001Block081Part022
    + surrogateDiagTailX0RatChunk000Sub001Block081Part023
    + surrogateDiagTailX0RatChunk000Sub001Block081Part024

def surrogateDiagonalTailChunk000Sub001Block081Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block081HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block081MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block081TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block081 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block081Part000
    + surrogateDiagTailX0RatChunk000Sub001Block081Part001
    + surrogateDiagTailX0RatChunk000Sub001Block081Part002
    + surrogateDiagTailX0RatChunk000Sub001Block081Part003
    + surrogateDiagTailX0RatChunk000Sub001Block081Part004
    + surrogateDiagTailX0RatChunk000Sub001Block081Part005
    + surrogateDiagTailX0RatChunk000Sub001Block081Part006
    + surrogateDiagTailX0RatChunk000Sub001Block081Part007
    + surrogateDiagTailX0RatChunk000Sub001Block081Part008
    + surrogateDiagTailX0RatChunk000Sub001Block081Part009
    + surrogateDiagTailX0RatChunk000Sub001Block081Part010
    + surrogateDiagTailX0RatChunk000Sub001Block081Part011
    + surrogateDiagTailX0RatChunk000Sub001Block081Part012
    + surrogateDiagTailX0RatChunk000Sub001Block081Part013
    + surrogateDiagTailX0RatChunk000Sub001Block081Part014
    + surrogateDiagTailX0RatChunk000Sub001Block081Part015
    + surrogateDiagTailX0RatChunk000Sub001Block081Part016
    + surrogateDiagTailX0RatChunk000Sub001Block081Part017
    + surrogateDiagTailX0RatChunk000Sub001Block081Part018
    + surrogateDiagTailX0RatChunk000Sub001Block081Part019
    + surrogateDiagTailX0RatChunk000Sub001Block081Part020
    + surrogateDiagTailX0RatChunk000Sub001Block081Part021
    + surrogateDiagTailX0RatChunk000Sub001Block081Part022
    + surrogateDiagTailX0RatChunk000Sub001Block081Part023
    + surrogateDiagTailX0RatChunk000Sub001Block081Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block081_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block081Head + surrogateDiagTailX0RatChunk000Sub001Block081Mid + surrogateDiagTailX0RatChunk000Sub001Block081Tail =
      surrogateDiagTailX0RatChunk000Sub001Block081 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block081Head surrogateDiagTailX0RatChunk000Sub001Block081Mid surrogateDiagTailX0RatChunk000Sub001Block081Tail surrogateDiagTailX0RatChunk000Sub001Block081
  ring

def SurrogateDiagonalTailChunk000Sub001Block081HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block081HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block081Head

def SurrogateDiagonalTailChunk000Sub001Block081MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block081MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block081Mid

def SurrogateDiagonalTailChunk000Sub001Block081TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block081TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block081Tail

theorem surrogateDiagonalTailChunk000Sub001Block081_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block081HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block081MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block081TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block081Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block081 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block081HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block081MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block081TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block081Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block081_eq_head_add_mid_add_tail

/-- Block 082 covers tail-support indices [7050,7075) and q from 11649 to 11690. -/

def TailChunk000Sub001Block082Part000SupportExplicit : Finset ℕ :=
  ([11649] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part000 : ℚ :=
  (979733229 : ℚ) / 1488996039393280

def SurrogateDiagonalTailChunk000Sub001Block082Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11649
    = surrogateDiagTailX0RatChunk000Sub001Block082Part000

theorem surrogateDiagonalTailChunk000Sub001Block082Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part000] using hcert

def TailChunk000Sub001Block082Part001SupportExplicit : Finset ℕ :=
  ([11651] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part001 : ℚ :=
  (109313575523 : ℚ) / 563099317344000000

def SurrogateDiagonalTailChunk000Sub001Block082Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11651
    = surrogateDiagTailX0RatChunk000Sub001Block082Part001

theorem surrogateDiagonalTailChunk000Sub001Block082Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part001] using hcert

def TailChunk000Sub001Block082Part002SupportExplicit : Finset ℕ :=
  ([11653] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part002 : ℚ :=
  (325153252183 : ℚ) / 1654013570502787200

def SurrogateDiagonalTailChunk000Sub001Block082Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11653
    = surrogateDiagTailX0RatChunk000Sub001Block082Part002

theorem surrogateDiagonalTailChunk000Sub001Block082Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part002] using hcert

def TailChunk000Sub001Block082Part003SupportExplicit : Finset ℕ :=
  ([11654] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part003 : ℚ :=
  (530530140625 : ℚ) / 720192822300117522

def SurrogateDiagonalTailChunk000Sub001Block082Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11654
    = surrogateDiagTailX0RatChunk000Sub001Block082Part003

theorem surrogateDiagonalTailChunk000Sub001Block082Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part003] using hcert

def TailChunk000Sub001Block082Part004SupportExplicit : Finset ℕ :=
  ([11657] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part004 : ℚ :=
  (2123213265625 : ℚ) / 11538916286403482112

def SurrogateDiagonalTailChunk000Sub001Block082Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11657
    = surrogateDiagTailX0RatChunk000Sub001Block082Part004

theorem surrogateDiagonalTailChunk000Sub001Block082Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part004] using hcert

def TailChunk000Sub001Block082Part005SupportExplicit : Finset ℕ :=
  ([11658] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part005 : ℚ :=
  (1124029035775 : ℚ) / 466610716715286528

def SurrogateDiagonalTailChunk000Sub001Block082Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11658
    = surrogateDiagTailX0RatChunk000Sub001Block082Part005

theorem surrogateDiagonalTailChunk000Sub001Block082Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part005] using hcert

def TailChunk000Sub001Block082Part006SupportExplicit : Finset ℕ :=
  ([11659] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part006 : ℚ :=
  (21992520453 : ℚ) / 114208831711969280

def SurrogateDiagonalTailChunk000Sub001Block082Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11659
    = surrogateDiagTailX0RatChunk000Sub001Block082Part006

theorem surrogateDiagonalTailChunk000Sub001Block082Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part006] using hcert

def TailChunk000Sub001Block082Part007SupportExplicit : Finset ℕ :=
  ([11663] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part007 : ℚ :=
  (1376260438975 : ℚ) / 7158039514698451968

def SurrogateDiagonalTailChunk000Sub001Block082Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11663
    = surrogateDiagTailX0RatChunk000Sub001Block082Part007

theorem surrogateDiagonalTailChunk000Sub001Block082Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part007] using hcert

def TailChunk000Sub001Block082Part008SupportExplicit : Finset ℕ :=
  ([11665] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part008 : ℚ :=
  (5779907184775 : ℚ) / 18931324883347734528

def SurrogateDiagonalTailChunk000Sub001Block082Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11665
    = surrogateDiagTailX0RatChunk000Sub001Block082Part008

theorem surrogateDiagonalTailChunk000Sub001Block082Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part008] using hcert

def TailChunk000Sub001Block082Part009SupportExplicit : Finset ℕ :=
  ([11666] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part009 : ℚ :=
  (1989900644875 : ℚ) / 2301455517233874048

def SurrogateDiagonalTailChunk000Sub001Block082Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11666
    = surrogateDiagTailX0RatChunk000Sub001Block082Part009

theorem surrogateDiagonalTailChunk000Sub001Block082Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part009] using hcert

def TailChunk000Sub001Block082Part010SupportExplicit : Finset ℕ :=
  ([11667] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part010 : ℚ :=
  (3779760611125 : ℚ) / 9142224179377471488

def SurrogateDiagonalTailChunk000Sub001Block082Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11667
    = surrogateDiagTailX0RatChunk000Sub001Block082Part010

theorem surrogateDiagonalTailChunk000Sub001Block082Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part010] using hcert

def TailChunk000Sub001Block082Part011SupportExplicit : Finset ℕ :=
  ([11669] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part011 : ℚ :=
  (7360022375 : ℚ) / 27862741069642143

def SurrogateDiagonalTailChunk000Sub001Block082Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11669
    = surrogateDiagTailX0RatChunk000Sub001Block082Part011

theorem surrogateDiagonalTailChunk000Sub001Block082Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part011] using hcert

def TailChunk000Sub001Block082Part012SupportExplicit : Finset ℕ :=
  ([11670] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part012 : ℚ :=
  (943513874575 : ℚ) / 232120613224316928

def SurrogateDiagonalTailChunk000Sub001Block082Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11670
    = surrogateDiagTailX0RatChunk000Sub001Block082Part012

theorem surrogateDiagonalTailChunk000Sub001Block082Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part012] using hcert

def TailChunk000Sub001Block082Part013SupportExplicit : Finset ℕ :=
  ([11671] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part013 : ℚ :=
  (289482197407 : ℚ) / 1262729455392000000

def SurrogateDiagonalTailChunk000Sub001Block082Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11671
    = surrogateDiagTailX0RatChunk000Sub001Block082Part013

theorem surrogateDiagonalTailChunk000Sub001Block082Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part013] using hcert

def TailChunk000Sub001Block082Part014SupportExplicit : Finset ℕ :=
  ([11674] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part014 : ℚ :=
  (645298996175 : ℚ) / 696213827166928896

def SurrogateDiagonalTailChunk000Sub001Block082Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11674
    = surrogateDiagTailX0RatChunk000Sub001Block082Part014

theorem surrogateDiagonalTailChunk000Sub001Block082Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part014] using hcert

def TailChunk000Sub001Block082Part015SupportExplicit : Finset ℕ :=
  ([11677] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part015 : ℚ :=
  (2130505140625 : ℚ) / 11618316759467511072

def SurrogateDiagonalTailChunk000Sub001Block082Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11677
    = surrogateDiagTailX0RatChunk000Sub001Block082Part015

theorem surrogateDiagonalTailChunk000Sub001Block082Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part015] using hcert

def TailChunk000Sub001Block082Part016SupportExplicit : Finset ℕ :=
  ([11678] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part016 : ℚ :=
  (532717515625 : ℚ) / 726144797466719442

def SurrogateDiagonalTailChunk000Sub001Block082Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11678
    = surrogateDiagTailX0RatChunk000Sub001Block082Part016

theorem surrogateDiagonalTailChunk000Sub001Block082Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part016] using hcert

def TailChunk000Sub001Block082Part017SupportExplicit : Finset ℕ :=
  ([11679] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part017 : ℚ :=
  (1736693588975 : ℚ) / 3542714578699812864

def SurrogateDiagonalTailChunk000Sub001Block082Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11679
    = surrogateDiagTailX0RatChunk000Sub001Block082Part017

theorem surrogateDiagonalTailChunk000Sub001Block082Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part017] using hcert

def TailChunk000Sub001Block082Part018SupportExplicit : Finset ℕ :=
  ([11681] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part018 : ℚ :=
  (3411144025 : ℚ) / 18614793436004352

def SurrogateDiagonalTailChunk000Sub001Block082Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11681
    = surrogateDiagTailX0RatChunk000Sub001Block082Part018

theorem surrogateDiagonalTailChunk000Sub001Block082Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part018] using hcert

def TailChunk000Sub001Block082Part019SupportExplicit : Finset ℕ :=
  ([11683] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part019 : ℚ :=
  (1652604595075 : ℚ) / 6271278017605120512

def SurrogateDiagonalTailChunk000Sub001Block082Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11683
    = surrogateDiagTailX0RatChunk000Sub001Block082Part019

theorem surrogateDiagonalTailChunk000Sub001Block082Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part019] using hcert

def TailChunk000Sub001Block082Part020SupportExplicit : Finset ℕ :=
  ([11685] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part020 : ℚ :=
  (3242205113 : ℚ) / 3440541538713600

def SurrogateDiagonalTailChunk000Sub001Block082Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11685
    = surrogateDiagTailX0RatChunk000Sub001Block082Part020

theorem surrogateDiagonalTailChunk000Sub001Block082Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part020] using hcert

def TailChunk000Sub001Block082Part021SupportExplicit : Finset ℕ :=
  ([11686] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part021 : ℚ :=
  (533447640625 : ℚ) / 728136963093774162

def SurrogateDiagonalTailChunk000Sub001Block082Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11686
    = surrogateDiagTailX0RatChunk000Sub001Block082Part021

theorem surrogateDiagonalTailChunk000Sub001Block082Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part021] using hcert

def TailChunk000Sub001Block082Part022SupportExplicit : Finset ℕ :=
  ([11687] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part022 : ℚ :=
  (897147133 : ℚ) / 3441975097688064

def SurrogateDiagonalTailChunk000Sub001Block082Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11687
    = surrogateDiagTailX0RatChunk000Sub001Block082Part022

theorem surrogateDiagonalTailChunk000Sub001Block082Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part022] using hcert

def TailChunk000Sub001Block082Part023SupportExplicit : Finset ℕ :=
  ([11689] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part023 : ℚ :=
  (2134886265625 : ℚ) / 11666153306677473792

def SurrogateDiagonalTailChunk000Sub001Block082Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11689
    = surrogateDiagTailX0RatChunk000Sub001Block082Part023

theorem surrogateDiagonalTailChunk000Sub001Block082Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part023] using hcert

def TailChunk000Sub001Block082Part024SupportExplicit : Finset ℕ :=
  ([11690] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block082Part024 : ℚ :=
  (4191231875 : ℚ) / 1944281606725632

def SurrogateDiagonalTailChunk000Sub001Block082Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11690
    = surrogateDiagTailX0RatChunk000Sub001Block082Part024

theorem surrogateDiagonalTailChunk000Sub001Block082Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block082Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block082Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block082Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block082Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block082Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block082HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block082Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block082Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block082Part000
    + surrogateDiagTailX0RatChunk000Sub001Block082Part001
    + surrogateDiagTailX0RatChunk000Sub001Block082Part002
    + surrogateDiagTailX0RatChunk000Sub001Block082Part003
    + surrogateDiagTailX0RatChunk000Sub001Block082Part004
    + surrogateDiagTailX0RatChunk000Sub001Block082Part005
    + surrogateDiagTailX0RatChunk000Sub001Block082Part006
    + surrogateDiagTailX0RatChunk000Sub001Block082Part007
    + surrogateDiagTailX0RatChunk000Sub001Block082Part008
    + surrogateDiagTailX0RatChunk000Sub001Block082Part009

def surrogateDiagonalTailChunk000Sub001Block082MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block082Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block082Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block082Part010
    + surrogateDiagTailX0RatChunk000Sub001Block082Part011
    + surrogateDiagTailX0RatChunk000Sub001Block082Part012
    + surrogateDiagTailX0RatChunk000Sub001Block082Part013
    + surrogateDiagTailX0RatChunk000Sub001Block082Part014
    + surrogateDiagTailX0RatChunk000Sub001Block082Part015
    + surrogateDiagTailX0RatChunk000Sub001Block082Part016
    + surrogateDiagTailX0RatChunk000Sub001Block082Part017
    + surrogateDiagTailX0RatChunk000Sub001Block082Part018
    + surrogateDiagTailX0RatChunk000Sub001Block082Part019

def surrogateDiagonalTailChunk000Sub001Block082TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block082Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block082Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block082Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block082Part020
    + surrogateDiagTailX0RatChunk000Sub001Block082Part021
    + surrogateDiagTailX0RatChunk000Sub001Block082Part022
    + surrogateDiagTailX0RatChunk000Sub001Block082Part023
    + surrogateDiagTailX0RatChunk000Sub001Block082Part024

def surrogateDiagonalTailChunk000Sub001Block082Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block082HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block082MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block082TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block082 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block082Part000
    + surrogateDiagTailX0RatChunk000Sub001Block082Part001
    + surrogateDiagTailX0RatChunk000Sub001Block082Part002
    + surrogateDiagTailX0RatChunk000Sub001Block082Part003
    + surrogateDiagTailX0RatChunk000Sub001Block082Part004
    + surrogateDiagTailX0RatChunk000Sub001Block082Part005
    + surrogateDiagTailX0RatChunk000Sub001Block082Part006
    + surrogateDiagTailX0RatChunk000Sub001Block082Part007
    + surrogateDiagTailX0RatChunk000Sub001Block082Part008
    + surrogateDiagTailX0RatChunk000Sub001Block082Part009
    + surrogateDiagTailX0RatChunk000Sub001Block082Part010
    + surrogateDiagTailX0RatChunk000Sub001Block082Part011
    + surrogateDiagTailX0RatChunk000Sub001Block082Part012
    + surrogateDiagTailX0RatChunk000Sub001Block082Part013
    + surrogateDiagTailX0RatChunk000Sub001Block082Part014
    + surrogateDiagTailX0RatChunk000Sub001Block082Part015
    + surrogateDiagTailX0RatChunk000Sub001Block082Part016
    + surrogateDiagTailX0RatChunk000Sub001Block082Part017
    + surrogateDiagTailX0RatChunk000Sub001Block082Part018
    + surrogateDiagTailX0RatChunk000Sub001Block082Part019
    + surrogateDiagTailX0RatChunk000Sub001Block082Part020
    + surrogateDiagTailX0RatChunk000Sub001Block082Part021
    + surrogateDiagTailX0RatChunk000Sub001Block082Part022
    + surrogateDiagTailX0RatChunk000Sub001Block082Part023
    + surrogateDiagTailX0RatChunk000Sub001Block082Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block082_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block082Head + surrogateDiagTailX0RatChunk000Sub001Block082Mid + surrogateDiagTailX0RatChunk000Sub001Block082Tail =
      surrogateDiagTailX0RatChunk000Sub001Block082 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block082Head surrogateDiagTailX0RatChunk000Sub001Block082Mid surrogateDiagTailX0RatChunk000Sub001Block082Tail surrogateDiagTailX0RatChunk000Sub001Block082
  ring

def SurrogateDiagonalTailChunk000Sub001Block082HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block082HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block082Head

def SurrogateDiagonalTailChunk000Sub001Block082MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block082MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block082Mid

def SurrogateDiagonalTailChunk000Sub001Block082TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block082TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block082Tail

theorem surrogateDiagonalTailChunk000Sub001Block082_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block082HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block082MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block082TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block082Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block082 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block082HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block082MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block082TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block082Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block082_eq_head_add_mid_add_tail

/-- Block 083 covers tail-support indices [7075,7100) and q from 11693 to 11731. -/

def TailChunk000Sub001Block083Part000SupportExplicit : Finset ℕ :=
  ([11693] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part000 : ℚ :=
  (293402653921 : ℚ) / 1272286494753667200

def SurrogateDiagonalTailChunk000Sub001Block083Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11693
    = surrogateDiagTailX0RatChunk000Sub001Block083Part000

theorem surrogateDiagonalTailChunk000Sub001Block083Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part000] using hcert

def TailChunk000Sub001Block083Part001SupportExplicit : Finset ℕ :=
  ([11694] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part001 : ℚ :=
  (142363875 : ℚ) / 57599113790464

def SurrogateDiagonalTailChunk000Sub001Block083Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11694
    = surrogateDiagTailX0RatChunk000Sub001Block083Part001

theorem surrogateDiagonalTailChunk000Sub001Block083Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part001] using hcert

def TailChunk000Sub001Block083Part002SupportExplicit : Finset ℕ :=
  ([11695] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part002 : ℚ :=
  (5809681237225 : ℚ) / 19126911636626884608

def SurrogateDiagonalTailChunk000Sub001Block083Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11695
    = surrogateDiagTailX0RatChunk000Sub001Block083Part002

theorem surrogateDiagonalTailChunk000Sub001Block083Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part002] using hcert

def TailChunk000Sub001Block083Part003SupportExplicit : Finset ℕ :=
  ([11697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part003 : ℚ :=
  (1528154090675 : ℚ) / 2477541932881035264

def SurrogateDiagonalTailChunk000Sub001Block083Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11697
    = surrogateDiagTailX0RatChunk000Sub001Block083Part003

theorem surrogateDiagonalTailChunk000Sub001Block083Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part003] using hcert

def TailChunk000Sub001Block083Part004SupportExplicit : Finset ℕ :=
  ([11698] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part004 : ℚ :=
  (534543765625 : ℚ) / 731132893841060352

def SurrogateDiagonalTailChunk000Sub001Block083Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11698
    = surrogateDiagTailX0RatChunk000Sub001Block083Part004

theorem surrogateDiagonalTailChunk000Sub001Block083Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part004] using hcert

def TailChunk000Sub001Block083Part005SupportExplicit : Finset ℕ :=
  ([11699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part005 : ℚ :=
  (2138540640625 : ℚ) / 11706129808426133202

def SurrogateDiagonalTailChunk000Sub001Block083Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11699
    = surrogateDiagTailX0RatChunk000Sub001Block083Part005

theorem surrogateDiagonalTailChunk000Sub001Block083Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part005] using hcert

def TailChunk000Sub001Block083Part006SupportExplicit : Finset ℕ :=
  ([11701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part006 : ℚ :=
  (136913401 : ℚ) / 749704794976800

def SurrogateDiagonalTailChunk000Sub001Block083Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11701
    = surrogateDiagTailX0RatChunk000Sub001Block083Part006

theorem surrogateDiagonalTailChunk000Sub001Block083Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part006] using hcert

def TailChunk000Sub001Block083Part007SupportExplicit : Finset ℕ :=
  ([11702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part007 : ℚ :=
  (34234201 : ℚ) / 46856549686050

def SurrogateDiagonalTailChunk000Sub001Block083Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11702
    = surrogateDiagTailX0RatChunk000Sub001Block083Part007

theorem surrogateDiagonalTailChunk000Sub001Block083Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part007] using hcert

def TailChunk000Sub001Block083Part008SupportExplicit : Finset ℕ :=
  ([11703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part008 : ℚ :=
  (3633682097575 : ℚ) / 8099040632399874048

def SurrogateDiagonalTailChunk000Sub001Block083Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11703
    = surrogateDiagTailX0RatChunk000Sub001Block083Part008

theorem surrogateDiagonalTailChunk000Sub001Block083Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part008] using hcert

def TailChunk000Sub001Block083Part009SupportExplicit : Finset ℕ :=
  ([11705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part009 : ℚ :=
  (232784916919 : ℚ) / 767697710056243200

def SurrogateDiagonalTailChunk000Sub001Block083Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11705
    = surrogateDiagTailX0RatChunk000Sub001Block083Part009

theorem surrogateDiagonalTailChunk000Sub001Block083Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part009] using hcert

def TailChunk000Sub001Block083Part010SupportExplicit : Finset ℕ :=
  ([11706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part010 : ℚ :=
  (11890962637 : ℚ) / 5784759220500000

def SurrogateDiagonalTailChunk000Sub001Block083Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11706
    = surrogateDiagTailX0RatChunk000Sub001Block083Part010

theorem surrogateDiagonalTailChunk000Sub001Block083Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part010] using hcert

def TailChunk000Sub001Block083Part011SupportExplicit : Finset ℕ :=
  ([11707] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part011 : ℚ :=
  (2653157386425 : ℚ) / 13003227970282756096

def SurrogateDiagonalTailChunk000Sub001Block083Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11707
    = surrogateDiagTailX0RatChunk000Sub001Block083Part011

theorem surrogateDiagonalTailChunk000Sub001Block083Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part011] using hcert

def TailChunk000Sub001Block083Part012SupportExplicit : Finset ℕ :=
  ([11710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part012 : ℚ :=
  (6850868899 : ℚ) / 4798110687851520

def SurrogateDiagonalTailChunk000Sub001Block083Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11710
    = surrogateDiagTailX0RatChunk000Sub001Block083Part012

theorem surrogateDiagonalTailChunk000Sub001Block083Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part012] using hcert

def TailChunk000Sub001Block083Part013SupportExplicit : Finset ℕ :=
  ([11713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part013 : ℚ :=
  (2221869411875 : ℚ) / 8281783889093984256

def SurrogateDiagonalTailChunk000Sub001Block083Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11713
    = surrogateDiagTailX0RatChunk000Sub001Block083Part013

theorem surrogateDiagonalTailChunk000Sub001Block083Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part013] using hcert

def TailChunk000Sub001Block083Part014SupportExplicit : Finset ℕ :=
  ([11714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part014 : ℚ :=
  (536007015625 : ℚ) / 735141837946355712

def SurrogateDiagonalTailChunk000Sub001Block083Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11714
    = surrogateDiagTailX0RatChunk000Sub001Block083Part014

theorem surrogateDiagonalTailChunk000Sub001Block083Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part014] using hcert

def TailChunk000Sub001Block083Part015SupportExplicit : Finset ℕ :=
  ([11715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part015 : ℚ :=
  (31773024579 : ℚ) / 32788209664000000

def SurrogateDiagonalTailChunk000Sub001Block083Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11715
    = surrogateDiagTailX0RatChunk000Sub001Block083Part015

theorem surrogateDiagonalTailChunk000Sub001Block083Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part015] using hcert

def TailChunk000Sub001Block083Part016SupportExplicit : Finset ℕ :=
  ([11717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part016 : ℚ :=
  (2145126390625 : ℚ) / 11778346314972309792

def SurrogateDiagonalTailChunk000Sub001Block083Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11717
    = surrogateDiagTailX0RatChunk000Sub001Block083Part016

theorem surrogateDiagonalTailChunk000Sub001Block083Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part016] using hcert

def TailChunk000Sub001Block083Part017SupportExplicit : Finset ℕ :=
  ([11719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part017 : ℚ :=
  (2145858765625 : ℚ) / 11786390946329510322

def SurrogateDiagonalTailChunk000Sub001Block083Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11719
    = surrogateDiagTailX0RatChunk000Sub001Block083Part017

theorem surrogateDiagonalTailChunk000Sub001Block083Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part017] using hcert

def TailChunk000Sub001Block083Part018SupportExplicit : Finset ℕ :=
  ([11721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part018 : ℚ :=
  (298071808225 : ℚ) / 582043997349605448

def SurrogateDiagonalTailChunk000Sub001Block083Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11721
    = surrogateDiagTailX0RatChunk000Sub001Block083Part018

theorem surrogateDiagonalTailChunk000Sub001Block083Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part018] using hcert

def TailChunk000Sub001Block083Part019SupportExplicit : Finset ℕ :=
  ([11722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part019 : ℚ :=
  (858783025 : ℚ) / 1179443969785632

def SurrogateDiagonalTailChunk000Sub001Block083Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11722
    = surrogateDiagTailX0RatChunk000Sub001Block083Part019

theorem surrogateDiagonalTailChunk000Sub001Block083Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part019] using hcert

def TailChunk000Sub001Block083Part020SupportExplicit : Finset ℕ :=
  ([11723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part020 : ℚ :=
  (1122370262275 : ℚ) / 5399352579134029824

def SurrogateDiagonalTailChunk000Sub001Block083Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11723
    = surrogateDiagTailX0RatChunk000Sub001Block083Part020

theorem surrogateDiagonalTailChunk000Sub001Block083Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part020] using hcert

def TailChunk000Sub001Block083Part021SupportExplicit : Finset ℕ :=
  ([11726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part021 : ℚ :=
  (6809285131 : ℚ) / 5309477683200000

def SurrogateDiagonalTailChunk000Sub001Block083Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11726
    = surrogateDiagTailX0RatChunk000Sub001Block083Part021

theorem surrogateDiagonalTailChunk000Sub001Block083Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part021] using hcert

def TailChunk000Sub001Block083Part022SupportExplicit : Finset ℕ :=
  ([11729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part022 : ℚ :=
  (33720954175 : ℚ) / 172337154856943616

def SurrogateDiagonalTailChunk000Sub001Block083Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11729
    = surrogateDiagTailX0RatChunk000Sub001Block083Part022

theorem surrogateDiagonalTailChunk000Sub001Block083Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part022] using hcert

def TailChunk000Sub001Block083Part023SupportExplicit : Finset ℕ :=
  ([11730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part023 : ℚ :=
  (488886833075 : ℚ) / 78618990879965184

def SurrogateDiagonalTailChunk000Sub001Block083Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11730
    = surrogateDiagTailX0RatChunk000Sub001Block083Part023

theorem surrogateDiagonalTailChunk000Sub001Block083Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part023] using hcert

def TailChunk000Sub001Block083Part024SupportExplicit : Finset ℕ :=
  ([11731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block083Part024 : ℚ :=
  (3440409025 : ℚ) / 18935592491636082

def SurrogateDiagonalTailChunk000Sub001Block083Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11731
    = surrogateDiagTailX0RatChunk000Sub001Block083Part024

theorem surrogateDiagonalTailChunk000Sub001Block083Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block083Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block083Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block083Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block083Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block083Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block083HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block083Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block083Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block083Part000
    + surrogateDiagTailX0RatChunk000Sub001Block083Part001
    + surrogateDiagTailX0RatChunk000Sub001Block083Part002
    + surrogateDiagTailX0RatChunk000Sub001Block083Part003
    + surrogateDiagTailX0RatChunk000Sub001Block083Part004
    + surrogateDiagTailX0RatChunk000Sub001Block083Part005
    + surrogateDiagTailX0RatChunk000Sub001Block083Part006
    + surrogateDiagTailX0RatChunk000Sub001Block083Part007
    + surrogateDiagTailX0RatChunk000Sub001Block083Part008
    + surrogateDiagTailX0RatChunk000Sub001Block083Part009

def surrogateDiagonalTailChunk000Sub001Block083MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block083Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block083Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block083Part010
    + surrogateDiagTailX0RatChunk000Sub001Block083Part011
    + surrogateDiagTailX0RatChunk000Sub001Block083Part012
    + surrogateDiagTailX0RatChunk000Sub001Block083Part013
    + surrogateDiagTailX0RatChunk000Sub001Block083Part014
    + surrogateDiagTailX0RatChunk000Sub001Block083Part015
    + surrogateDiagTailX0RatChunk000Sub001Block083Part016
    + surrogateDiagTailX0RatChunk000Sub001Block083Part017
    + surrogateDiagTailX0RatChunk000Sub001Block083Part018
    + surrogateDiagTailX0RatChunk000Sub001Block083Part019

def surrogateDiagonalTailChunk000Sub001Block083TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block083Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block083Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block083Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block083Part020
    + surrogateDiagTailX0RatChunk000Sub001Block083Part021
    + surrogateDiagTailX0RatChunk000Sub001Block083Part022
    + surrogateDiagTailX0RatChunk000Sub001Block083Part023
    + surrogateDiagTailX0RatChunk000Sub001Block083Part024

def surrogateDiagonalTailChunk000Sub001Block083Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block083HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block083MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block083TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block083 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block083Part000
    + surrogateDiagTailX0RatChunk000Sub001Block083Part001
    + surrogateDiagTailX0RatChunk000Sub001Block083Part002
    + surrogateDiagTailX0RatChunk000Sub001Block083Part003
    + surrogateDiagTailX0RatChunk000Sub001Block083Part004
    + surrogateDiagTailX0RatChunk000Sub001Block083Part005
    + surrogateDiagTailX0RatChunk000Sub001Block083Part006
    + surrogateDiagTailX0RatChunk000Sub001Block083Part007
    + surrogateDiagTailX0RatChunk000Sub001Block083Part008
    + surrogateDiagTailX0RatChunk000Sub001Block083Part009
    + surrogateDiagTailX0RatChunk000Sub001Block083Part010
    + surrogateDiagTailX0RatChunk000Sub001Block083Part011
    + surrogateDiagTailX0RatChunk000Sub001Block083Part012
    + surrogateDiagTailX0RatChunk000Sub001Block083Part013
    + surrogateDiagTailX0RatChunk000Sub001Block083Part014
    + surrogateDiagTailX0RatChunk000Sub001Block083Part015
    + surrogateDiagTailX0RatChunk000Sub001Block083Part016
    + surrogateDiagTailX0RatChunk000Sub001Block083Part017
    + surrogateDiagTailX0RatChunk000Sub001Block083Part018
    + surrogateDiagTailX0RatChunk000Sub001Block083Part019
    + surrogateDiagTailX0RatChunk000Sub001Block083Part020
    + surrogateDiagTailX0RatChunk000Sub001Block083Part021
    + surrogateDiagTailX0RatChunk000Sub001Block083Part022
    + surrogateDiagTailX0RatChunk000Sub001Block083Part023
    + surrogateDiagTailX0RatChunk000Sub001Block083Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block083_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block083Head + surrogateDiagTailX0RatChunk000Sub001Block083Mid + surrogateDiagTailX0RatChunk000Sub001Block083Tail =
      surrogateDiagTailX0RatChunk000Sub001Block083 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block083Head surrogateDiagTailX0RatChunk000Sub001Block083Mid surrogateDiagTailX0RatChunk000Sub001Block083Tail surrogateDiagTailX0RatChunk000Sub001Block083
  ring

def SurrogateDiagonalTailChunk000Sub001Block083HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block083HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block083Head

def SurrogateDiagonalTailChunk000Sub001Block083MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block083MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block083Mid

def SurrogateDiagonalTailChunk000Sub001Block083TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block083TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block083Tail

theorem surrogateDiagonalTailChunk000Sub001Block083_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block083HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block083MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block083TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block083Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block083 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block083HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block083MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block083TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block083Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block083_eq_head_add_mid_add_tail

/-- Block 084 covers tail-support indices [7100,7125) and q from 11733 to 11773. -/

def TailChunk000Sub001Block084Part000SupportExplicit : Finset ℕ :=
  ([11733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part000 : ℚ :=
  (47789204947 : ℚ) / 93509098724128800

def SurrogateDiagonalTailChunk000Sub001Block084Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11733
    = surrogateDiagTailX0RatChunk000Sub001Block084Part000

theorem surrogateDiagonalTailChunk000Sub001Block084Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part000] using hcert

def TailChunk000Sub001Block084Part001SupportExplicit : Finset ℕ :=
  ([11734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part001 : ℚ :=
  (537838890625 : ℚ) / 740176175585200242

def SurrogateDiagonalTailChunk000Sub001Block084Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11734
    = surrogateDiagTailX0RatChunk000Sub001Block084Part001

theorem surrogateDiagonalTailChunk000Sub001Block084Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part001] using hcert

def TailChunk000Sub001Block084Part002SupportExplicit : Finset ℕ :=
  ([11735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part002 : ℚ :=
  (5849498985025 : ℚ) / 19390046711435347968

def SurrogateDiagonalTailChunk000Sub001Block084Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11735
    = surrogateDiagTailX0RatChunk000Sub001Block084Part002

theorem surrogateDiagonalTailChunk000Sub001Block084Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part002] using hcert

def TailChunk000Sub001Block084Part003SupportExplicit : Finset ℕ :=
  ([11738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part003 : ℚ :=
  (538205640625 : ℚ) / 741186137813405472

def SurrogateDiagonalTailChunk000Sub001Block084Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11738
    = surrogateDiagTailX0RatChunk000Sub001Block084Part003

theorem surrogateDiagonalTailChunk000Sub001Block084Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part003] using hcert

def TailChunk000Sub001Block084Part004SupportExplicit : Finset ℕ :=
  ([11739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part004 : ℚ :=
  (3243195159025 : ℚ) / 3345599794952798208

def SurrogateDiagonalTailChunk000Sub001Block084Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11739
    = surrogateDiagTailX0RatChunk000Sub001Block084Part004

theorem surrogateDiagonalTailChunk000Sub001Block084Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part004] using hcert

def TailChunk000Sub001Block084Part005SupportExplicit : Finset ℕ :=
  ([11741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part005 : ℚ :=
  (4160253881975 : ℚ) / 21745510041923832384

def SurrogateDiagonalTailChunk000Sub001Block084Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11741
    = surrogateDiagTailX0RatChunk000Sub001Block084Part005

theorem surrogateDiagonalTailChunk000Sub001Block084Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part005] using hcert

def TailChunk000Sub001Block084Part006SupportExplicit : Finset ℕ :=
  ([11742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part006 : ℚ :=
  (667006028525 : ℚ) / 227304248615691264

def SurrogateDiagonalTailChunk000Sub001Block084Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11742
    = surrogateDiagTailX0RatChunk000Sub001Block084Part006

theorem surrogateDiagonalTailChunk000Sub001Block084Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part006] using hcert

def TailChunk000Sub001Block084Part007SupportExplicit : Finset ℕ :=
  ([11743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part007 : ℚ :=
  (2154657015625 : ℚ) / 11883248298293583762

def SurrogateDiagonalTailChunk000Sub001Block084Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11743
    = surrogateDiagTailX0RatChunk000Sub001Block084Part007

theorem surrogateDiagonalTailChunk000Sub001Block084Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part007] using hcert

def TailChunk000Sub001Block084Part008SupportExplicit : Finset ℕ :=
  ([11746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part008 : ℚ :=
  (3679891925 : ℚ) / 22196036918839824

def SurrogateDiagonalTailChunk000Sub001Block084Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11746
    = surrogateDiagTailX0RatChunk000Sub001Block084Part008

theorem surrogateDiagonalTailChunk000Sub001Block084Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part008] using hcert

def TailChunk000Sub001Block084Part009SupportExplicit : Finset ℕ :=
  ([11747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part009 : ℚ :=
  (4260841277 : ℚ) / 742904772172185600

def SurrogateDiagonalTailChunk000Sub001Block084Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11747
    = surrogateDiagTailX0RatChunk000Sub001Block084Part009

theorem surrogateDiagonalTailChunk000Sub001Block084Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part009] using hcert

def TailChunk000Sub001Block084Part010SupportExplicit : Finset ℕ :=
  ([11749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part010 : ℚ :=
  (111265837 : ℚ) / 36755857122284160

def SurrogateDiagonalTailChunk000Sub001Block084Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11749
    = surrogateDiagTailX0RatChunk000Sub001Block084Part010

theorem surrogateDiagonalTailChunk000Sub001Block084Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part010] using hcert

def TailChunk000Sub001Block084Part011SupportExplicit : Finset ℕ :=
  ([11751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part011 : ℚ :=
  (7492703825 : ℚ) / 73503429784887696

def SurrogateDiagonalTailChunk000Sub001Block084Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11751
    = surrogateDiagTailX0RatChunk000Sub001Block084Part011

theorem surrogateDiagonalTailChunk000Sub001Block084Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part011] using hcert

def TailChunk000Sub001Block084Part012SupportExplicit : Finset ℕ :=
  ([11753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part012 : ℚ :=
  (645762886525 : ℚ) / 20401052310663856128

def SurrogateDiagonalTailChunk000Sub001Block084Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11753
    = surrogateDiagTailX0RatChunk000Sub001Block084Part012

theorem surrogateDiagonalTailChunk000Sub001Block084Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part012] using hcert

def TailChunk000Sub001Block084Part013SupportExplicit : Finset ℕ :=
  ([11755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part013 : ℚ :=
  (588446687 : ℚ) / 16615002336000000

def SurrogateDiagonalTailChunk000Sub001Block084Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11755
    = surrogateDiagTailX0RatChunk000Sub001Block084Part013

theorem surrogateDiagonalTailChunk000Sub001Block084Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part013] using hcert

def TailChunk000Sub001Block084Part014SupportExplicit : Finset ℕ :=
  ([11757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part014 : ℚ :=
  (480022669775 : ℚ) / 4713837125392816704

def SurrogateDiagonalTailChunk000Sub001Block084Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11757
    = surrogateDiagTailX0RatChunk000Sub001Block084Part014

theorem surrogateDiagonalTailChunk000Sub001Block084Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part014] using hcert

def TailChunk000Sub001Block084Part015SupportExplicit : Finset ℕ :=
  ([11758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block084Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11758
    = surrogateDiagTailX0RatChunk000Sub001Block084Part015

theorem surrogateDiagonalTailChunk000Sub001Block084Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part015] using hcert

def TailChunk000Sub001Block084Part016SupportExplicit : Finset ℕ :=
  ([11759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part016 : ℚ :=
  (239524553 : ℚ) / 21688055233297920

def SurrogateDiagonalTailChunk000Sub001Block084Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11759
    = surrogateDiagTailX0RatChunk000Sub001Block084Part016

theorem surrogateDiagonalTailChunk000Sub001Block084Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part016] using hcert

def TailChunk000Sub001Block084Part017SupportExplicit : Finset ℕ :=
  ([11761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part017 : ℚ :=
  (196316657875 : ℚ) / 38288713971245378688

def SurrogateDiagonalTailChunk000Sub001Block084Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11761
    = surrogateDiagTailX0RatChunk000Sub001Block084Part017

theorem surrogateDiagonalTailChunk000Sub001Block084Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part017] using hcert

def TailChunk000Sub001Block084Part018SupportExplicit : Finset ℕ :=
  ([11762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part018 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block084Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11762
    = surrogateDiagTailX0RatChunk000Sub001Block084Part018

theorem surrogateDiagonalTailChunk000Sub001Block084Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part018] using hcert

def TailChunk000Sub001Block084Part019SupportExplicit : Finset ℕ :=
  ([11765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part019 : ℚ :=
  (925483963 : ℚ) / 15482436924211200

def SurrogateDiagonalTailChunk000Sub001Block084Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11765
    = surrogateDiagTailX0RatChunk000Sub001Block084Part019

theorem surrogateDiagonalTailChunk000Sub001Block084Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part019] using hcert

def TailChunk000Sub001Block084Part020SupportExplicit : Finset ℕ :=
  ([11766] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part020 : ℚ :=
  (1367663130325 : ℚ) / 491326534435995648

def SurrogateDiagonalTailChunk000Sub001Block084Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11766
    = surrogateDiagTailX0RatChunk000Sub001Block084Part020

theorem surrogateDiagonalTailChunk000Sub001Block084Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part020] using hcert

def TailChunk000Sub001Block084Part021SupportExplicit : Finset ℕ :=
  ([11769] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part021 : ℚ :=
  (481002669725 : ℚ) / 4733116597693852224

def SurrogateDiagonalTailChunk000Sub001Block084Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11769
    = surrogateDiagTailX0RatChunk000Sub001Block084Part021

theorem surrogateDiagonalTailChunk000Sub001Block084Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part021] using hcert

def TailChunk000Sub001Block084Part022SupportExplicit : Finset ℕ :=
  ([11770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part022 : ℚ :=
  (61237886371 : ℚ) / 32325874058035200

def SurrogateDiagonalTailChunk000Sub001Block084Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11770
    = surrogateDiagTailX0RatChunk000Sub001Block084Part022

theorem surrogateDiagonalTailChunk000Sub001Block084Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part022] using hcert

def TailChunk000Sub001Block084Part023SupportExplicit : Finset ℕ :=
  ([11771] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part023 : ℚ :=
  (119095675 : ℚ) / 75011944651772544

def SurrogateDiagonalTailChunk000Sub001Block084Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11771
    = surrogateDiagTailX0RatChunk000Sub001Block084Part023

theorem surrogateDiagonalTailChunk000Sub001Block084Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part023] using hcert

def TailChunk000Sub001Block084Part024SupportExplicit : Finset ℕ :=
  ([11773] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block084Part024 : ℚ :=
  (58044937 : ℚ) / 32621430885580800

def SurrogateDiagonalTailChunk000Sub001Block084Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11773
    = surrogateDiagTailX0RatChunk000Sub001Block084Part024

theorem surrogateDiagonalTailChunk000Sub001Block084Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block084Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block084Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block084Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block084Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block084Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block084HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block084Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block084Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block084Part000
    + surrogateDiagTailX0RatChunk000Sub001Block084Part001
    + surrogateDiagTailX0RatChunk000Sub001Block084Part002
    + surrogateDiagTailX0RatChunk000Sub001Block084Part003
    + surrogateDiagTailX0RatChunk000Sub001Block084Part004
    + surrogateDiagTailX0RatChunk000Sub001Block084Part005
    + surrogateDiagTailX0RatChunk000Sub001Block084Part006
    + surrogateDiagTailX0RatChunk000Sub001Block084Part007
    + surrogateDiagTailX0RatChunk000Sub001Block084Part008
    + surrogateDiagTailX0RatChunk000Sub001Block084Part009

def surrogateDiagonalTailChunk000Sub001Block084MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block084Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block084Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block084Part010
    + surrogateDiagTailX0RatChunk000Sub001Block084Part011
    + surrogateDiagTailX0RatChunk000Sub001Block084Part012
    + surrogateDiagTailX0RatChunk000Sub001Block084Part013
    + surrogateDiagTailX0RatChunk000Sub001Block084Part014
    + surrogateDiagTailX0RatChunk000Sub001Block084Part015
    + surrogateDiagTailX0RatChunk000Sub001Block084Part016
    + surrogateDiagTailX0RatChunk000Sub001Block084Part017
    + surrogateDiagTailX0RatChunk000Sub001Block084Part018
    + surrogateDiagTailX0RatChunk000Sub001Block084Part019

def surrogateDiagonalTailChunk000Sub001Block084TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block084Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block084Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block084Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block084Part020
    + surrogateDiagTailX0RatChunk000Sub001Block084Part021
    + surrogateDiagTailX0RatChunk000Sub001Block084Part022
    + surrogateDiagTailX0RatChunk000Sub001Block084Part023
    + surrogateDiagTailX0RatChunk000Sub001Block084Part024

def surrogateDiagonalTailChunk000Sub001Block084Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block084HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block084MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block084TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block084 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block084Part000
    + surrogateDiagTailX0RatChunk000Sub001Block084Part001
    + surrogateDiagTailX0RatChunk000Sub001Block084Part002
    + surrogateDiagTailX0RatChunk000Sub001Block084Part003
    + surrogateDiagTailX0RatChunk000Sub001Block084Part004
    + surrogateDiagTailX0RatChunk000Sub001Block084Part005
    + surrogateDiagTailX0RatChunk000Sub001Block084Part006
    + surrogateDiagTailX0RatChunk000Sub001Block084Part007
    + surrogateDiagTailX0RatChunk000Sub001Block084Part008
    + surrogateDiagTailX0RatChunk000Sub001Block084Part009
    + surrogateDiagTailX0RatChunk000Sub001Block084Part010
    + surrogateDiagTailX0RatChunk000Sub001Block084Part011
    + surrogateDiagTailX0RatChunk000Sub001Block084Part012
    + surrogateDiagTailX0RatChunk000Sub001Block084Part013
    + surrogateDiagTailX0RatChunk000Sub001Block084Part014
    + surrogateDiagTailX0RatChunk000Sub001Block084Part015
    + surrogateDiagTailX0RatChunk000Sub001Block084Part016
    + surrogateDiagTailX0RatChunk000Sub001Block084Part017
    + surrogateDiagTailX0RatChunk000Sub001Block084Part018
    + surrogateDiagTailX0RatChunk000Sub001Block084Part019
    + surrogateDiagTailX0RatChunk000Sub001Block084Part020
    + surrogateDiagTailX0RatChunk000Sub001Block084Part021
    + surrogateDiagTailX0RatChunk000Sub001Block084Part022
    + surrogateDiagTailX0RatChunk000Sub001Block084Part023
    + surrogateDiagTailX0RatChunk000Sub001Block084Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block084_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block084Head + surrogateDiagTailX0RatChunk000Sub001Block084Mid + surrogateDiagTailX0RatChunk000Sub001Block084Tail =
      surrogateDiagTailX0RatChunk000Sub001Block084 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block084Head surrogateDiagTailX0RatChunk000Sub001Block084Mid surrogateDiagTailX0RatChunk000Sub001Block084Tail surrogateDiagTailX0RatChunk000Sub001Block084
  ring

def SurrogateDiagonalTailChunk000Sub001Block084HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block084HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block084Head

def SurrogateDiagonalTailChunk000Sub001Block084MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block084MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block084Mid

def SurrogateDiagonalTailChunk000Sub001Block084TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block084TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block084Tail

theorem surrogateDiagonalTailChunk000Sub001Block084_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block084HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block084MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block084TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block084Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block084 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block084HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block084MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block084TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block084Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block084_eq_head_add_mid_add_tail

/-- Block 085 covers tail-support indices [7125,7150) and q from 11777 to 11814. -/

def TailChunk000Sub001Block085Part000SupportExplicit : Finset ℕ :=
  ([11777] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part000 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11777
    = surrogateDiagTailX0RatChunk000Sub001Block085Part000

theorem surrogateDiagonalTailChunk000Sub001Block085Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part000] using hcert

def TailChunk000Sub001Block085Part001SupportExplicit : Finset ℕ :=
  ([11778] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part001 : ℚ :=
  (26141533469 : ℚ) / 8399759616000000

def SurrogateDiagonalTailChunk000Sub001Block085Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11778
    = surrogateDiagTailX0RatChunk000Sub001Block085Part001

theorem surrogateDiagonalTailChunk000Sub001Block085Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part001] using hcert

def TailChunk000Sub001Block085Part002SupportExplicit : Finset ℕ :=
  ([11779] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part002 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11779
    = surrogateDiagTailX0RatChunk000Sub001Block085Part002

theorem surrogateDiagonalTailChunk000Sub001Block085Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part002] using hcert

def TailChunk000Sub001Block085Part003SupportExplicit : Finset ℕ :=
  ([11782] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part003 : ℚ :=
  (454492825 : ℚ) / 577653200018496

def SurrogateDiagonalTailChunk000Sub001Block085Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11782
    = surrogateDiagTailX0RatChunk000Sub001Block085Part003

theorem surrogateDiagonalTailChunk000Sub001Block085Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part003] using hcert

def TailChunk000Sub001Block085Part004SupportExplicit : Finset ℕ :=
  ([11783] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11783
    = surrogateDiagTailX0RatChunk000Sub001Block085Part004

theorem surrogateDiagonalTailChunk000Sub001Block085Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part004] using hcert

def TailChunk000Sub001Block085Part005SupportExplicit : Finset ℕ :=
  ([11785] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part005 : ℚ :=
  (694953649525 : ℚ) / 19722772656463577088

def SurrogateDiagonalTailChunk000Sub001Block085Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11785
    = surrogateDiagTailX0RatChunk000Sub001Block085Part005

theorem surrogateDiagonalTailChunk000Sub001Block085Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part005] using hcert

def TailChunk000Sub001Block085Part006SupportExplicit : Finset ℕ :=
  ([11786] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part006 : ℚ :=
  (3008379217 : ℚ) / 3877719480818400

def SurrogateDiagonalTailChunk000Sub001Block085Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11786
    = surrogateDiagTailX0RatChunk000Sub001Block085Part006

theorem surrogateDiagonalTailChunk000Sub001Block085Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part006] using hcert

def TailChunk000Sub001Block085Part007SupportExplicit : Finset ℕ :=
  ([11787] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part007 : ℚ :=
  (241237272325 : ℚ) / 2381073308496371712

def SurrogateDiagonalTailChunk000Sub001Block085Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11787
    = surrogateDiagTailX0RatChunk000Sub001Block085Part007

theorem surrogateDiagonalTailChunk000Sub001Block085Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part007] using hcert

def TailChunk000Sub001Block085Part008SupportExplicit : Finset ℕ :=
  ([11789] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11789
    = surrogateDiagTailX0RatChunk000Sub001Block085Part008

theorem surrogateDiagonalTailChunk000Sub001Block085Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part008] using hcert

def TailChunk000Sub001Block085Part009SupportExplicit : Finset ℕ :=
  ([11791] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part009 : ℚ :=
  (28895439875 : ℚ) / 3881701401084168192

def SurrogateDiagonalTailChunk000Sub001Block085Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11791
    = surrogateDiagTailX0RatChunk000Sub001Block085Part009

theorem surrogateDiagonalTailChunk000Sub001Block085Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part009] using hcert

def TailChunk000Sub001Block085Part010SupportExplicit : Finset ℕ :=
  ([11793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part010 : ℚ :=
  (3863725357 : ℚ) / 38174823199552320

def SurrogateDiagonalTailChunk000Sub001Block085Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11793
    = surrogateDiagTailX0RatChunk000Sub001Block085Part010

theorem surrogateDiagonalTailChunk000Sub001Block085Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part010] using hcert

def TailChunk000Sub001Block085Part011SupportExplicit : Finset ℕ :=
  ([11794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part011 : ℚ :=
  (543353265625 : ℚ) / 755434416828191232

def SurrogateDiagonalTailChunk000Sub001Block085Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11794
    = surrogateDiagTailX0RatChunk000Sub001Block085Part011

theorem surrogateDiagonalTailChunk000Sub001Block085Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part011] using hcert

def TailChunk000Sub001Block085Part012SupportExplicit : Finset ℕ :=
  ([11795] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part012 : ℚ :=
  (65074584275 : ℚ) / 587430416672096256

def SurrogateDiagonalTailChunk000Sub001Block085Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11795
    = surrogateDiagTailX0RatChunk000Sub001Block085Part012

theorem surrogateDiagonalTailChunk000Sub001Block085Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part012] using hcert

def TailChunk000Sub001Block085Part013SupportExplicit : Finset ℕ :=
  ([11797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part013 : ℚ :=
  (1765553543 : ℚ) / 874678025625000000

def SurrogateDiagonalTailChunk000Sub001Block085Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11797
    = surrogateDiagTailX0RatChunk000Sub001Block085Part013

theorem surrogateDiagonalTailChunk000Sub001Block085Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part013] using hcert

def TailChunk000Sub001Block085Part014SupportExplicit : Finset ℕ :=
  ([11798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part014 : ℚ :=
  (1012793888825 : ℚ) / 1174305754327547904

def SurrogateDiagonalTailChunk000Sub001Block085Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11798
    = surrogateDiagTailX0RatChunk000Sub001Block085Part014

theorem surrogateDiagonalTailChunk000Sub001Block085Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part014] using hcert

def TailChunk000Sub001Block085Part015SupportExplicit : Finset ℕ :=
  ([11801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11801
    = surrogateDiagTailX0RatChunk000Sub001Block085Part015

theorem surrogateDiagonalTailChunk000Sub001Block085Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part015] using hcert

def TailChunk000Sub001Block085Part016SupportExplicit : Finset ℕ :=
  ([11802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part016 : ℚ :=
  (41511794041 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub001Block085Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11802
    = surrogateDiagTailX0RatChunk000Sub001Block085Part016

theorem surrogateDiagonalTailChunk000Sub001Block085Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part016] using hcert

def TailChunk000Sub001Block085Part017SupportExplicit : Finset ℕ :=
  ([11803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part017 : ℚ :=
  (5127554281 : ℚ) / 258148132326604800

def SurrogateDiagonalTailChunk000Sub001Block085Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11803
    = surrogateDiagTailX0RatChunk000Sub001Block085Part017

theorem surrogateDiagonalTailChunk000Sub001Block085Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part017] using hcert

def TailChunk000Sub001Block085Part018SupportExplicit : Finset ℕ :=
  ([11805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part018 : ℚ :=
  (1045045623025 : ℚ) / 3909101895634157568

def SurrogateDiagonalTailChunk000Sub001Block085Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11805
    = surrogateDiagTailX0RatChunk000Sub001Block085Part018

theorem surrogateDiagonalTailChunk000Sub001Block085Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part018] using hcert

def TailChunk000Sub001Block085Part019SupportExplicit : Finset ℕ :=
  ([11806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part019 : ℚ :=
  (544459515625 : ℚ) / 758514152263963602

def SurrogateDiagonalTailChunk000Sub001Block085Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11806
    = surrogateDiagTailX0RatChunk000Sub001Block085Part019

theorem surrogateDiagonalTailChunk000Sub001Block085Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part019] using hcert

def TailChunk000Sub001Block085Part020SupportExplicit : Finset ℕ :=
  ([11807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part020 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11807
    = surrogateDiagTailX0RatChunk000Sub001Block085Part020

theorem surrogateDiagonalTailChunk000Sub001Block085Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part020] using hcert

def TailChunk000Sub001Block085Part021SupportExplicit : Finset ℕ :=
  ([11810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part021 : ℚ :=
  (33100768817 : ℚ) / 24821318599065600

def SurrogateDiagonalTailChunk000Sub001Block085Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11810
    = surrogateDiagTailX0RatChunk000Sub001Block085Part021

theorem surrogateDiagonalTailChunk000Sub001Block085Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part021] using hcert

def TailChunk000Sub001Block085Part022SupportExplicit : Finset ℕ :=
  ([11811] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part022 : ℚ :=
  (1129304789 : ℚ) / 9334820856453120

def SurrogateDiagonalTailChunk000Sub001Block085Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11811
    = surrogateDiagTailX0RatChunk000Sub001Block085Part022

theorem surrogateDiagonalTailChunk000Sub001Block085Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part022] using hcert

def TailChunk000Sub001Block085Part023SupportExplicit : Finset ℕ :=
  ([11813] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part023 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block085Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11813
    = surrogateDiagTailX0RatChunk000Sub001Block085Part023

theorem surrogateDiagonalTailChunk000Sub001Block085Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part023] using hcert

def TailChunk000Sub001Block085Part024SupportExplicit : Finset ℕ :=
  ([11814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block085Part024 : ℚ :=
  (17222154039 : ℚ) / 5355075366246400

def SurrogateDiagonalTailChunk000Sub001Block085Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11814
    = surrogateDiagTailX0RatChunk000Sub001Block085Part024

theorem surrogateDiagonalTailChunk000Sub001Block085Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block085Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block085Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block085Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block085Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block085Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block085HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block085Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block085Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block085Part000
    + surrogateDiagTailX0RatChunk000Sub001Block085Part001
    + surrogateDiagTailX0RatChunk000Sub001Block085Part002
    + surrogateDiagTailX0RatChunk000Sub001Block085Part003
    + surrogateDiagTailX0RatChunk000Sub001Block085Part004
    + surrogateDiagTailX0RatChunk000Sub001Block085Part005
    + surrogateDiagTailX0RatChunk000Sub001Block085Part006
    + surrogateDiagTailX0RatChunk000Sub001Block085Part007
    + surrogateDiagTailX0RatChunk000Sub001Block085Part008
    + surrogateDiagTailX0RatChunk000Sub001Block085Part009

def surrogateDiagonalTailChunk000Sub001Block085MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block085Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block085Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block085Part010
    + surrogateDiagTailX0RatChunk000Sub001Block085Part011
    + surrogateDiagTailX0RatChunk000Sub001Block085Part012
    + surrogateDiagTailX0RatChunk000Sub001Block085Part013
    + surrogateDiagTailX0RatChunk000Sub001Block085Part014
    + surrogateDiagTailX0RatChunk000Sub001Block085Part015
    + surrogateDiagTailX0RatChunk000Sub001Block085Part016
    + surrogateDiagTailX0RatChunk000Sub001Block085Part017
    + surrogateDiagTailX0RatChunk000Sub001Block085Part018
    + surrogateDiagTailX0RatChunk000Sub001Block085Part019

def surrogateDiagonalTailChunk000Sub001Block085TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block085Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block085Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block085Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block085Part020
    + surrogateDiagTailX0RatChunk000Sub001Block085Part021
    + surrogateDiagTailX0RatChunk000Sub001Block085Part022
    + surrogateDiagTailX0RatChunk000Sub001Block085Part023
    + surrogateDiagTailX0RatChunk000Sub001Block085Part024

def surrogateDiagonalTailChunk000Sub001Block085Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block085HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block085MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block085TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block085 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block085Part000
    + surrogateDiagTailX0RatChunk000Sub001Block085Part001
    + surrogateDiagTailX0RatChunk000Sub001Block085Part002
    + surrogateDiagTailX0RatChunk000Sub001Block085Part003
    + surrogateDiagTailX0RatChunk000Sub001Block085Part004
    + surrogateDiagTailX0RatChunk000Sub001Block085Part005
    + surrogateDiagTailX0RatChunk000Sub001Block085Part006
    + surrogateDiagTailX0RatChunk000Sub001Block085Part007
    + surrogateDiagTailX0RatChunk000Sub001Block085Part008
    + surrogateDiagTailX0RatChunk000Sub001Block085Part009
    + surrogateDiagTailX0RatChunk000Sub001Block085Part010
    + surrogateDiagTailX0RatChunk000Sub001Block085Part011
    + surrogateDiagTailX0RatChunk000Sub001Block085Part012
    + surrogateDiagTailX0RatChunk000Sub001Block085Part013
    + surrogateDiagTailX0RatChunk000Sub001Block085Part014
    + surrogateDiagTailX0RatChunk000Sub001Block085Part015
    + surrogateDiagTailX0RatChunk000Sub001Block085Part016
    + surrogateDiagTailX0RatChunk000Sub001Block085Part017
    + surrogateDiagTailX0RatChunk000Sub001Block085Part018
    + surrogateDiagTailX0RatChunk000Sub001Block085Part019
    + surrogateDiagTailX0RatChunk000Sub001Block085Part020
    + surrogateDiagTailX0RatChunk000Sub001Block085Part021
    + surrogateDiagTailX0RatChunk000Sub001Block085Part022
    + surrogateDiagTailX0RatChunk000Sub001Block085Part023
    + surrogateDiagTailX0RatChunk000Sub001Block085Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block085_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block085Head + surrogateDiagTailX0RatChunk000Sub001Block085Mid + surrogateDiagTailX0RatChunk000Sub001Block085Tail =
      surrogateDiagTailX0RatChunk000Sub001Block085 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block085Head surrogateDiagTailX0RatChunk000Sub001Block085Mid surrogateDiagTailX0RatChunk000Sub001Block085Tail surrogateDiagTailX0RatChunk000Sub001Block085
  ring

def SurrogateDiagonalTailChunk000Sub001Block085HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block085HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block085Head

def SurrogateDiagonalTailChunk000Sub001Block085MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block085MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block085Mid

def SurrogateDiagonalTailChunk000Sub001Block085TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block085TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block085Tail

theorem surrogateDiagonalTailChunk000Sub001Block085_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block085HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block085MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block085TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block085Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block085 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block085HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block085MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block085TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block085Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block085_eq_head_add_mid_add_tail

/-- Block 086 covers tail-support indices [7150,7175) and q from 11815 to 11859. -/

def TailChunk000Sub001Block086Part000SupportExplicit : Finset ℕ :=
  ([11815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part000 : ℚ :=
  (794747845675 : ℚ) / 15214689734086361088

def SurrogateDiagonalTailChunk000Sub001Block086Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11815
    = surrogateDiagTailX0RatChunk000Sub001Block086Part000

theorem surrogateDiagonalTailChunk000Sub001Block086Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part000] using hcert

def TailChunk000Sub001Block086Part001SupportExplicit : Finset ℕ :=
  ([11818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part001 : ℚ :=
  (81684672271 : ℚ) / 96966930004099200

def SurrogateDiagonalTailChunk000Sub001Block086Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11818
    = surrogateDiagTailX0RatChunk000Sub001Block086Part001

theorem surrogateDiagonalTailChunk000Sub001Block086Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part001] using hcert

def TailChunk000Sub001Block086Part002SupportExplicit : Finset ℕ :=
  ([11819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part002 : ℚ :=
  (41918765075 : ℚ) / 22203535616924673024

def SurrogateDiagonalTailChunk000Sub001Block086Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11819
    = surrogateDiagTailX0RatChunk000Sub001Block086Part002

theorem surrogateDiagonalTailChunk000Sub001Block086Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part002] using hcert

def TailChunk000Sub001Block086Part003SupportExplicit : Finset ℕ :=
  ([11821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part003 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block086Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11821
    = surrogateDiagTailX0RatChunk000Sub001Block086Part003

theorem surrogateDiagonalTailChunk000Sub001Block086Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part003] using hcert

def TailChunk000Sub001Block086Part004SupportExplicit : Finset ℕ :=
  ([11822] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part004 : ℚ :=
  (687807670575 : ℚ) / 838602569386295296

def SurrogateDiagonalTailChunk000Sub001Block086Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11822
    = surrogateDiagTailX0RatChunk000Sub001Block086Part004

theorem surrogateDiagonalTailChunk000Sub001Block086Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part004] using hcert

def TailChunk000Sub001Block086Part005SupportExplicit : Finset ℕ :=
  ([11823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part005 : ℚ :=
  (20514647725 : ℚ) / 63857525646379008

def SurrogateDiagonalTailChunk000Sub001Block086Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11823
    = surrogateDiagTailX0RatChunk000Sub001Block086Part005

theorem surrogateDiagonalTailChunk000Sub001Block086Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part005] using hcert

def TailChunk000Sub001Block086Part006SupportExplicit : Finset ℕ :=
  ([11827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part006 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block086Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11827
    = surrogateDiagTailX0RatChunk000Sub001Block086Part006

theorem surrogateDiagonalTailChunk000Sub001Block086Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part006] using hcert

def TailChunk000Sub001Block086Part007SupportExplicit : Finset ℕ :=
  ([11829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part007 : ℚ :=
  (971328373325 : ℚ) / 4830402557824017984

def SurrogateDiagonalTailChunk000Sub001Block086Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11829
    = surrogateDiagTailX0RatChunk000Sub001Block086Part007

theorem surrogateDiagonalTailChunk000Sub001Block086Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part007] using hcert

def TailChunk000Sub001Block086Part008SupportExplicit : Finset ℕ :=
  ([11831] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block086Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11831
    = surrogateDiagTailX0RatChunk000Sub001Block086Part008

theorem surrogateDiagonalTailChunk000Sub001Block086Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part008] using hcert

def TailChunk000Sub001Block086Part009SupportExplicit : Finset ℕ :=
  ([11833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block086Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11833
    = surrogateDiagTailX0RatChunk000Sub001Block086Part009

theorem surrogateDiagonalTailChunk000Sub001Block086Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part009] using hcert

def TailChunk000Sub001Block086Part010SupportExplicit : Finset ℕ :=
  ([11834] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part010 : ℚ :=
  (1697536037 : ℚ) / 2201946584776704

def SurrogateDiagonalTailChunk000Sub001Block086Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11834
    = surrogateDiagTailX0RatChunk000Sub001Block086Part010

theorem surrogateDiagonalTailChunk000Sub001Block086Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part010] using hcert

def TailChunk000Sub001Block086Part011SupportExplicit : Finset ℕ :=
  ([11837] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part011 : ℚ :=
  (221726844425 : ℚ) / 6800350770221285376

def SurrogateDiagonalTailChunk000Sub001Block086Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11837
    = surrogateDiagTailX0RatChunk000Sub001Block086Part011

theorem surrogateDiagonalTailChunk000Sub001Block086Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part011] using hcert

def TailChunk000Sub001Block086Part012SupportExplicit : Finset ℕ :=
  ([11838] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part012 : ℚ :=
  (608032163675 : ℚ) / 302513310537114624

def SurrogateDiagonalTailChunk000Sub001Block086Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11838
    = surrogateDiagTailX0RatChunk000Sub001Block086Part012

theorem surrogateDiagonalTailChunk000Sub001Block086Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part012] using hcert

def TailChunk000Sub001Block086Part013SupportExplicit : Finset ℕ :=
  ([11839] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part013 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block086Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11839
    = surrogateDiagTailX0RatChunk000Sub001Block086Part013

theorem surrogateDiagonalTailChunk000Sub001Block086Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part013] using hcert

def TailChunk000Sub001Block086Part014SupportExplicit : Finset ℕ :=
  ([11841] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part014 : ℚ :=
  (486903669425 : ℚ) / 4850038315281436224

def SurrogateDiagonalTailChunk000Sub001Block086Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11841
    = surrogateDiagTailX0RatChunk000Sub001Block086Part014

theorem surrogateDiagonalTailChunk000Sub001Block086Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part014] using hcert

def TailChunk000Sub001Block086Part015SupportExplicit : Finset ℕ :=
  ([11842] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part015 : ℚ :=
  (16773918509 : ℚ) / 21116224400400000

def SurrogateDiagonalTailChunk000Sub001Block086Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11842
    = surrogateDiagTailX0RatChunk000Sub001Block086Part015

theorem surrogateDiagonalTailChunk000Sub001Block086Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part015] using hcert

def TailChunk000Sub001Block086Part016SupportExplicit : Finset ℕ :=
  ([11843] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part016 : ℚ :=
  (502367155 : ℚ) / 56890191414970368

def SurrogateDiagonalTailChunk000Sub001Block086Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11843
    = surrogateDiagTailX0RatChunk000Sub001Block086Part016

theorem surrogateDiagonalTailChunk000Sub001Block086Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part016] using hcert

def TailChunk000Sub001Block086Part017SupportExplicit : Finset ℕ :=
  ([11845] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part017 : ℚ :=
  (784386970225 : ℚ) / 16231484244388773888

def SurrogateDiagonalTailChunk000Sub001Block086Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11845
    = surrogateDiagTailX0RatChunk000Sub001Block086Part017

theorem surrogateDiagonalTailChunk000Sub001Block086Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part017] using hcert

def TailChunk000Sub001Block086Part018SupportExplicit : Finset ℕ :=
  ([11846] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part018 : ℚ :=
  (548155140625 : ℚ) / 768847983703380882

def SurrogateDiagonalTailChunk000Sub001Block086Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11846
    = surrogateDiagTailX0RatChunk000Sub001Block086Part018

theorem surrogateDiagonalTailChunk000Sub001Block086Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part018] using hcert

def TailChunk000Sub001Block086Part019SupportExplicit : Finset ℕ :=
  ([11847] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part019 : ℚ :=
  (40304220001 : ℚ) / 262868737570867200

def SurrogateDiagonalTailChunk000Sub001Block086Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11847
    = surrogateDiagTailX0RatChunk000Sub001Block086Part019

theorem surrogateDiagonalTailChunk000Sub001Block086Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part019] using hcert

def TailChunk000Sub001Block086Part020SupportExplicit : Finset ℕ :=
  ([11851] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part020 : ℚ :=
  (9971239075 : ℚ) / 491857768833149952

def SurrogateDiagonalTailChunk000Sub001Block086Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11851
    = surrogateDiagTailX0RatChunk000Sub001Block086Part020

theorem surrogateDiagonalTailChunk000Sub001Block086Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part020] using hcert

def TailChunk000Sub001Block086Part021SupportExplicit : Finset ℕ :=
  ([11854] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part021 : ℚ :=
  (548895765625 : ℚ) / 770927355021686322

def SurrogateDiagonalTailChunk000Sub001Block086Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11854
    = surrogateDiagTailX0RatChunk000Sub001Block086Part021

theorem surrogateDiagonalTailChunk000Sub001Block086Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part021] using hcert

def TailChunk000Sub001Block086Part022SupportExplicit : Finset ℕ :=
  ([11855] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part022 : ℚ :=
  (9376299883 : ℚ) / 269276804463974400

def SurrogateDiagonalTailChunk000Sub001Block086Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11855
    = surrogateDiagTailX0RatChunk000Sub001Block086Part022

theorem surrogateDiagonalTailChunk000Sub001Block086Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part022] using hcert

def TailChunk000Sub001Block086Part023SupportExplicit : Finset ℕ :=
  ([11857] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part023 : ℚ :=
  (952186947 : ℚ) / 607841163769302400

def SurrogateDiagonalTailChunk000Sub001Block086Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11857
    = surrogateDiagTailX0RatChunk000Sub001Block086Part023

theorem surrogateDiagonalTailChunk000Sub001Block086Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part023] using hcert

def TailChunk000Sub001Block086Part024SupportExplicit : Finset ℕ :=
  ([11859] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block086Part024 : ℚ :=
  (9194106425 : ℚ) / 79544618351801856

def SurrogateDiagonalTailChunk000Sub001Block086Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11859
    = surrogateDiagTailX0RatChunk000Sub001Block086Part024

theorem surrogateDiagonalTailChunk000Sub001Block086Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block086Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block086Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block086Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block086Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block086Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block086HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block086Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block086Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block086Part000
    + surrogateDiagTailX0RatChunk000Sub001Block086Part001
    + surrogateDiagTailX0RatChunk000Sub001Block086Part002
    + surrogateDiagTailX0RatChunk000Sub001Block086Part003
    + surrogateDiagTailX0RatChunk000Sub001Block086Part004
    + surrogateDiagTailX0RatChunk000Sub001Block086Part005
    + surrogateDiagTailX0RatChunk000Sub001Block086Part006
    + surrogateDiagTailX0RatChunk000Sub001Block086Part007
    + surrogateDiagTailX0RatChunk000Sub001Block086Part008
    + surrogateDiagTailX0RatChunk000Sub001Block086Part009

def surrogateDiagonalTailChunk000Sub001Block086MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block086Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block086Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block086Part010
    + surrogateDiagTailX0RatChunk000Sub001Block086Part011
    + surrogateDiagTailX0RatChunk000Sub001Block086Part012
    + surrogateDiagTailX0RatChunk000Sub001Block086Part013
    + surrogateDiagTailX0RatChunk000Sub001Block086Part014
    + surrogateDiagTailX0RatChunk000Sub001Block086Part015
    + surrogateDiagTailX0RatChunk000Sub001Block086Part016
    + surrogateDiagTailX0RatChunk000Sub001Block086Part017
    + surrogateDiagTailX0RatChunk000Sub001Block086Part018
    + surrogateDiagTailX0RatChunk000Sub001Block086Part019

def surrogateDiagonalTailChunk000Sub001Block086TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block086Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block086Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block086Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block086Part020
    + surrogateDiagTailX0RatChunk000Sub001Block086Part021
    + surrogateDiagTailX0RatChunk000Sub001Block086Part022
    + surrogateDiagTailX0RatChunk000Sub001Block086Part023
    + surrogateDiagTailX0RatChunk000Sub001Block086Part024

def surrogateDiagonalTailChunk000Sub001Block086Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block086HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block086MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block086TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block086 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block086Part000
    + surrogateDiagTailX0RatChunk000Sub001Block086Part001
    + surrogateDiagTailX0RatChunk000Sub001Block086Part002
    + surrogateDiagTailX0RatChunk000Sub001Block086Part003
    + surrogateDiagTailX0RatChunk000Sub001Block086Part004
    + surrogateDiagTailX0RatChunk000Sub001Block086Part005
    + surrogateDiagTailX0RatChunk000Sub001Block086Part006
    + surrogateDiagTailX0RatChunk000Sub001Block086Part007
    + surrogateDiagTailX0RatChunk000Sub001Block086Part008
    + surrogateDiagTailX0RatChunk000Sub001Block086Part009
    + surrogateDiagTailX0RatChunk000Sub001Block086Part010
    + surrogateDiagTailX0RatChunk000Sub001Block086Part011
    + surrogateDiagTailX0RatChunk000Sub001Block086Part012
    + surrogateDiagTailX0RatChunk000Sub001Block086Part013
    + surrogateDiagTailX0RatChunk000Sub001Block086Part014
    + surrogateDiagTailX0RatChunk000Sub001Block086Part015
    + surrogateDiagTailX0RatChunk000Sub001Block086Part016
    + surrogateDiagTailX0RatChunk000Sub001Block086Part017
    + surrogateDiagTailX0RatChunk000Sub001Block086Part018
    + surrogateDiagTailX0RatChunk000Sub001Block086Part019
    + surrogateDiagTailX0RatChunk000Sub001Block086Part020
    + surrogateDiagTailX0RatChunk000Sub001Block086Part021
    + surrogateDiagTailX0RatChunk000Sub001Block086Part022
    + surrogateDiagTailX0RatChunk000Sub001Block086Part023
    + surrogateDiagTailX0RatChunk000Sub001Block086Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block086_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block086Head + surrogateDiagTailX0RatChunk000Sub001Block086Mid + surrogateDiagTailX0RatChunk000Sub001Block086Tail =
      surrogateDiagTailX0RatChunk000Sub001Block086 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block086Head surrogateDiagTailX0RatChunk000Sub001Block086Mid surrogateDiagTailX0RatChunk000Sub001Block086Tail surrogateDiagTailX0RatChunk000Sub001Block086
  ring

def SurrogateDiagonalTailChunk000Sub001Block086HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block086HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block086Head

def SurrogateDiagonalTailChunk000Sub001Block086MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block086MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block086Mid

def SurrogateDiagonalTailChunk000Sub001Block086TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block086TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block086Tail

theorem surrogateDiagonalTailChunk000Sub001Block086_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block086HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block086MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block086TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block086Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block086 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block086HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block086MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block086TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block086Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block086_eq_head_add_mid_add_tail

/-- Block 087 covers tail-support indices [7175,7200) and q from 11861 to 11901. -/

def TailChunk000Sub001Block087Part000SupportExplicit : Finset ℕ :=
  ([11861] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part000 : ℚ :=
  (33326066275 : ℚ) / 10647303782740918272

def SurrogateDiagonalTailChunk000Sub001Block087Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11861
    = surrogateDiagTailX0RatChunk000Sub001Block087Part000

theorem surrogateDiagonalTailChunk000Sub001Block087Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part000] using hcert

def TailChunk000Sub001Block087Part001SupportExplicit : Finset ℕ :=
  ([11863] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block087Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11863
    = surrogateDiagTailX0RatChunk000Sub001Block087Part001

theorem surrogateDiagonalTailChunk000Sub001Block087Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part001] using hcert

def TailChunk000Sub001Block087Part002SupportExplicit : Finset ℕ :=
  ([11865] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part002 : ℚ :=
  (259521778975 : ℚ) / 522160370375196672

def SurrogateDiagonalTailChunk000Sub001Block087Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11865
    = surrogateDiagTailX0RatChunk000Sub001Block087Part002

theorem surrogateDiagonalTailChunk000Sub001Block087Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part002] using hcert

def TailChunk000Sub001Block087Part003SupportExplicit : Finset ℕ :=
  ([11866] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part003 : ℚ :=
  (680478934075 : ℚ) / 801129106186960896

def SurrogateDiagonalTailChunk000Sub001Block087Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11866
    = surrogateDiagTailX0RatChunk000Sub001Block087Part003

theorem surrogateDiagonalTailChunk000Sub001Block087Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part003] using hcert

def TailChunk000Sub001Block087Part004SupportExplicit : Finset ℕ :=
  ([11867] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part004 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block087Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11867
    = surrogateDiagTailX0RatChunk000Sub001Block087Part004

theorem surrogateDiagonalTailChunk000Sub001Block087Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part004] using hcert

def TailChunk000Sub001Block087Part005SupportExplicit : Finset ℕ :=
  ([11869] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part005 : ℚ :=
  (8166173177 : ℚ) / 312569061824102400

def SurrogateDiagonalTailChunk000Sub001Block087Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11869
    = surrogateDiagTailX0RatChunk000Sub001Block087Part005

theorem surrogateDiagonalTailChunk000Sub001Block087Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part005] using hcert

def TailChunk000Sub001Block087Part006SupportExplicit : Finset ℕ :=
  ([11870] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part006 : ℚ :=
  (208987423175 : ℚ) / 158312640774195456

def SurrogateDiagonalTailChunk000Sub001Block087Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11870
    = surrogateDiagTailX0RatChunk000Sub001Block087Part006

theorem surrogateDiagonalTailChunk000Sub001Block087Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part006] using hcert

def TailChunk000Sub001Block087Part007SupportExplicit : Finset ℕ :=
  ([11873] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part007 : ℚ :=
  (5105525389 : ℚ) / 1725143875639171200

def SurrogateDiagonalTailChunk000Sub001Block087Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11873
    = surrogateDiagTailX0RatChunk000Sub001Block087Part007

theorem surrogateDiagonalTailChunk000Sub001Block087Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part007] using hcert

def TailChunk000Sub001Block087Part008SupportExplicit : Finset ℕ :=
  ([11874] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part008 : ℚ :=
  (146780625 : ℚ) / 61230124201024

def SurrogateDiagonalTailChunk000Sub001Block087Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11874
    = surrogateDiagTailX0RatChunk000Sub001Block087Part008

theorem surrogateDiagonalTailChunk000Sub001Block087Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part008] using hcert

def TailChunk000Sub001Block087Part009SupportExplicit : Finset ℕ :=
  ([11877] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part009 : ℚ :=
  (998511924325 : ℚ) / 8483602387790757888

def SurrogateDiagonalTailChunk000Sub001Block087Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11877
    = surrogateDiagTailX0RatChunk000Sub001Block087Part009

theorem surrogateDiagonalTailChunk000Sub001Block087Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part009] using hcert

def TailChunk000Sub001Block087Part010SupportExplicit : Finset ℕ :=
  ([11878] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part010 : ℚ :=
  (551120640625 : ℚ) / 777190781390073042

def SurrogateDiagonalTailChunk000Sub001Block087Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11878
    = surrogateDiagTailX0RatChunk000Sub001Block087Part010

theorem surrogateDiagonalTailChunk000Sub001Block087Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part010] using hcert

def TailChunk000Sub001Block087Part011SupportExplicit : Finset ℕ :=
  ([11879] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part011 : ℚ :=
  (30054827425 : ℚ) / 1489576276594262016

def SurrogateDiagonalTailChunk000Sub001Block087Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11879
    = surrogateDiagTailX0RatChunk000Sub001Block087Part011

theorem surrogateDiagonalTailChunk000Sub001Block087Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part011] using hcert

def TailChunk000Sub001Block087Part012SupportExplicit : Finset ℕ :=
  ([11882] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part012 : ℚ :=
  (2005518549325 : ℚ) / 2241874069333475328

def SurrogateDiagonalTailChunk000Sub001Block087Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11882
    = surrogateDiagTailX0RatChunk000Sub001Block087Part012

theorem surrogateDiagonalTailChunk000Sub001Block087Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part012] using hcert

def TailChunk000Sub001Block087Part013SupportExplicit : Finset ℕ :=
  ([11883] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part013 : ℚ :=
  (506239257575 : ℚ) / 3797945392293740544

def SurrogateDiagonalTailChunk000Sub001Block087Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11883
    = surrogateDiagTailX0RatChunk000Sub001Block087Part013

theorem surrogateDiagonalTailChunk000Sub001Block087Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part013] using hcert

def TailChunk000Sub001Block087Part014SupportExplicit : Finset ℕ :=
  ([11885] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part014 : ℚ :=
  (235593759175 : ℚ) / 6800350770221285376

def SurrogateDiagonalTailChunk000Sub001Block087Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11885
    = surrogateDiagTailX0RatChunk000Sub001Block087Part014

theorem surrogateDiagonalTailChunk000Sub001Block087Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part014] using hcert

def TailChunk000Sub001Block087Part015SupportExplicit : Finset ℕ :=
  ([11886] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part015 : ℚ :=
  (132624662425 : ℚ) / 81976294805524992

def SurrogateDiagonalTailChunk000Sub001Block087Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11886
    = surrogateDiagTailX0RatChunk000Sub001Block087Part015

theorem surrogateDiagonalTailChunk000Sub001Block087Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part015] using hcert

def TailChunk000Sub001Block087Part016SupportExplicit : Finset ℕ :=
  ([11887] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part016 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block087Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11887
    = surrogateDiagTailX0RatChunk000Sub001Block087Part016

theorem surrogateDiagonalTailChunk000Sub001Block087Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part016] using hcert

def TailChunk000Sub001Block087Part017SupportExplicit : Finset ℕ :=
  ([11890] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part017 : ℚ :=
  (3956137783 : ℚ) / 10072538008780800

def SurrogateDiagonalTailChunk000Sub001Block087Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11890
    = surrogateDiagTailX0RatChunk000Sub001Block087Part017

theorem surrogateDiagonalTailChunk000Sub001Block087Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part017] using hcert

def TailChunk000Sub001Block087Part018SupportExplicit : Finset ℕ :=
  ([11891] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part018 : ℚ :=
  (5202472837 : ℚ) / 262270176730636800

def SurrogateDiagonalTailChunk000Sub001Block087Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11891
    = surrogateDiagTailX0RatChunk000Sub001Block087Part018

theorem surrogateDiagonalTailChunk000Sub001Block087Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part018] using hcert

def TailChunk000Sub001Block087Part019SupportExplicit : Finset ℕ :=
  ([11893] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part019 : ℚ :=
  (10041835825 : ℚ) / 498871672720627392

def SurrogateDiagonalTailChunk000Sub001Block087Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11893
    = surrogateDiagTailX0RatChunk000Sub001Block087Part019

theorem surrogateDiagonalTailChunk000Sub001Block087Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part019] using hcert

def TailChunk000Sub001Block087Part020SupportExplicit : Finset ℕ :=
  ([11894] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part020 : ℚ :=
  (11408051975 : ℚ) / 276371175620247552

def SurrogateDiagonalTailChunk000Sub001Block087Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11894
    = surrogateDiagTailX0RatChunk000Sub001Block087Part020

theorem surrogateDiagonalTailChunk000Sub001Block087Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part020] using hcert

def TailChunk000Sub001Block087Part021SupportExplicit : Finset ℕ :=
  ([11895] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part021 : ℚ :=
  (20790792731 : ℚ) / 55048664619417600

def SurrogateDiagonalTailChunk000Sub001Block087Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11895
    = surrogateDiagTailX0RatChunk000Sub001Block087Part021

theorem surrogateDiagonalTailChunk000Sub001Block087Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part021] using hcert

def TailChunk000Sub001Block087Part022SupportExplicit : Finset ℕ :=
  ([11897] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block087Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11897
    = surrogateDiagTailX0RatChunk000Sub001Block087Part022

theorem surrogateDiagonalTailChunk000Sub001Block087Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part022] using hcert

def TailChunk000Sub001Block087Part023SupportExplicit : Finset ℕ :=
  ([11899] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part023 : ℚ :=
  (2699491075 : ℚ) / 1714167033633275904

def SurrogateDiagonalTailChunk000Sub001Block087Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11899
    = surrogateDiagTailX0RatChunk000Sub001Block087Part023

theorem surrogateDiagonalTailChunk000Sub001Block087Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part023] using hcert

def TailChunk000Sub001Block087Part024SupportExplicit : Finset ℕ :=
  ([11901] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block087Part024 : ℚ :=
  (491848669175 : ℚ) / 4949116594840609344

def SurrogateDiagonalTailChunk000Sub001Block087Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11901
    = surrogateDiagTailX0RatChunk000Sub001Block087Part024

theorem surrogateDiagonalTailChunk000Sub001Block087Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block087Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block087Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block087Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block087Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block087Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block087HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block087Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block087Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block087Part000
    + surrogateDiagTailX0RatChunk000Sub001Block087Part001
    + surrogateDiagTailX0RatChunk000Sub001Block087Part002
    + surrogateDiagTailX0RatChunk000Sub001Block087Part003
    + surrogateDiagTailX0RatChunk000Sub001Block087Part004
    + surrogateDiagTailX0RatChunk000Sub001Block087Part005
    + surrogateDiagTailX0RatChunk000Sub001Block087Part006
    + surrogateDiagTailX0RatChunk000Sub001Block087Part007
    + surrogateDiagTailX0RatChunk000Sub001Block087Part008
    + surrogateDiagTailX0RatChunk000Sub001Block087Part009

def surrogateDiagonalTailChunk000Sub001Block087MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block087Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block087Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block087Part010
    + surrogateDiagTailX0RatChunk000Sub001Block087Part011
    + surrogateDiagTailX0RatChunk000Sub001Block087Part012
    + surrogateDiagTailX0RatChunk000Sub001Block087Part013
    + surrogateDiagTailX0RatChunk000Sub001Block087Part014
    + surrogateDiagTailX0RatChunk000Sub001Block087Part015
    + surrogateDiagTailX0RatChunk000Sub001Block087Part016
    + surrogateDiagTailX0RatChunk000Sub001Block087Part017
    + surrogateDiagTailX0RatChunk000Sub001Block087Part018
    + surrogateDiagTailX0RatChunk000Sub001Block087Part019

def surrogateDiagonalTailChunk000Sub001Block087TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block087Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block087Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block087Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block087Part020
    + surrogateDiagTailX0RatChunk000Sub001Block087Part021
    + surrogateDiagTailX0RatChunk000Sub001Block087Part022
    + surrogateDiagTailX0RatChunk000Sub001Block087Part023
    + surrogateDiagTailX0RatChunk000Sub001Block087Part024

def surrogateDiagonalTailChunk000Sub001Block087Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block087HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block087MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block087TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block087 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block087Part000
    + surrogateDiagTailX0RatChunk000Sub001Block087Part001
    + surrogateDiagTailX0RatChunk000Sub001Block087Part002
    + surrogateDiagTailX0RatChunk000Sub001Block087Part003
    + surrogateDiagTailX0RatChunk000Sub001Block087Part004
    + surrogateDiagTailX0RatChunk000Sub001Block087Part005
    + surrogateDiagTailX0RatChunk000Sub001Block087Part006
    + surrogateDiagTailX0RatChunk000Sub001Block087Part007
    + surrogateDiagTailX0RatChunk000Sub001Block087Part008
    + surrogateDiagTailX0RatChunk000Sub001Block087Part009
    + surrogateDiagTailX0RatChunk000Sub001Block087Part010
    + surrogateDiagTailX0RatChunk000Sub001Block087Part011
    + surrogateDiagTailX0RatChunk000Sub001Block087Part012
    + surrogateDiagTailX0RatChunk000Sub001Block087Part013
    + surrogateDiagTailX0RatChunk000Sub001Block087Part014
    + surrogateDiagTailX0RatChunk000Sub001Block087Part015
    + surrogateDiagTailX0RatChunk000Sub001Block087Part016
    + surrogateDiagTailX0RatChunk000Sub001Block087Part017
    + surrogateDiagTailX0RatChunk000Sub001Block087Part018
    + surrogateDiagTailX0RatChunk000Sub001Block087Part019
    + surrogateDiagTailX0RatChunk000Sub001Block087Part020
    + surrogateDiagTailX0RatChunk000Sub001Block087Part021
    + surrogateDiagTailX0RatChunk000Sub001Block087Part022
    + surrogateDiagTailX0RatChunk000Sub001Block087Part023
    + surrogateDiagTailX0RatChunk000Sub001Block087Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block087_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block087Head + surrogateDiagTailX0RatChunk000Sub001Block087Mid + surrogateDiagTailX0RatChunk000Sub001Block087Tail =
      surrogateDiagTailX0RatChunk000Sub001Block087 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block087Head surrogateDiagTailX0RatChunk000Sub001Block087Mid surrogateDiagTailX0RatChunk000Sub001Block087Tail surrogateDiagTailX0RatChunk000Sub001Block087
  ring

def SurrogateDiagonalTailChunk000Sub001Block087HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block087HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block087Head

def SurrogateDiagonalTailChunk000Sub001Block087MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block087MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block087Mid

def SurrogateDiagonalTailChunk000Sub001Block087TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block087TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block087Tail

theorem surrogateDiagonalTailChunk000Sub001Block087_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block087HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block087MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block087TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block087Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block087 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block087HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block087MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block087TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block087Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block087_eq_head_add_mid_add_tail

/-- Block 088 covers tail-support indices [7200,7225) and q from 11902 to 11939. -/

def TailChunk000Sub001Block088Part000SupportExplicit : Finset ℕ :=
  ([11902] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part000 : ℚ :=
  (3337778327 : ℚ) / 42523783056000000

def SurrogateDiagonalTailChunk000Sub001Block088Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11902
    = surrogateDiagTailX0RatChunk000Sub001Block088Part000

theorem surrogateDiagonalTailChunk000Sub001Block088Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part000] using hcert

def TailChunk000Sub001Block088Part001SupportExplicit : Finset ℕ :=
  ([11903] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part001 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub001Block088Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11903
    = surrogateDiagTailX0RatChunk000Sub001Block088Part001

theorem surrogateDiagonalTailChunk000Sub001Block088Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part001] using hcert

def TailChunk000Sub001Block088Part002SupportExplicit : Finset ℕ :=
  ([11905] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part002 : ℚ :=
  (12142269777 : ℚ) / 39121486562099200

def SurrogateDiagonalTailChunk000Sub001Block088Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11905
    = surrogateDiagTailX0RatChunk000Sub001Block088Part002

theorem surrogateDiagonalTailChunk000Sub001Block088Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part002] using hcert

def TailChunk000Sub001Block088Part003SupportExplicit : Finset ℕ :=
  ([11906] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part003 : ℚ :=
  (553722015625 : ℚ) / 784546262314647552

def SurrogateDiagonalTailChunk000Sub001Block088Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11906
    = surrogateDiagTailX0RatChunk000Sub001Block088Part003

theorem surrogateDiagonalTailChunk000Sub001Block088Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part003] using hcert

def TailChunk000Sub001Block088Part004SupportExplicit : Finset ℕ :=
  ([11909] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part004 : ℚ :=
  (2216004390625 : ℚ) / 12569620665583386912

def SurrogateDiagonalTailChunk000Sub001Block088Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11909
    = surrogateDiagTailX0RatChunk000Sub001Block088Part004

theorem surrogateDiagonalTailChunk000Sub001Block088Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part004] using hcert

def TailChunk000Sub001Block088Part005SupportExplicit : Finset ℕ :=
  ([11910] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part005 : ℚ :=
  (579617434475 : ℚ) / 125932421670764544

def SurrogateDiagonalTailChunk000Sub001Block088Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11910
    = surrogateDiagTailX0RatChunk000Sub001Block088Part005

theorem surrogateDiagonalTailChunk000Sub001Block088Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part005] using hcert

def TailChunk000Sub001Block088Part006SupportExplicit : Finset ℕ :=
  ([11911] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part006 : ℚ :=
  (8493538411525 : ℚ) / 45150269686505883648

def SurrogateDiagonalTailChunk000Sub001Block088Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11911
    = surrogateDiagTailX0RatChunk000Sub001Block088Part006

theorem surrogateDiagonalTailChunk000Sub001Block088Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part006] using hcert

def TailChunk000Sub001Block088Part007SupportExplicit : Finset ℕ :=
  ([11914] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part007 : ℚ :=
  (1709064995725 : ℚ) / 1275065769416491008

def SurrogateDiagonalTailChunk000Sub001Block088Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11914
    = surrogateDiagTailX0RatChunk000Sub001Block088Part007

theorem surrogateDiagonalTailChunk000Sub001Block088Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part007] using hcert

def TailChunk000Sub001Block088Part008SupportExplicit : Finset ℕ :=
  ([11915] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part008 : ℚ :=
  (6030362008525 : ℚ) / 20607905433912035328

def SurrogateDiagonalTailChunk000Sub001Block088Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11915
    = surrogateDiagTailX0RatChunk000Sub001Block088Part008

theorem surrogateDiagonalTailChunk000Sub001Block088Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part008] using hcert

def TailChunk000Sub001Block088Part009SupportExplicit : Finset ℕ :=
  ([11917] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part009 : ℚ :=
  (32118891127 : ℚ) / 157383406387200000

def SurrogateDiagonalTailChunk000Sub001Block088Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11917
    = surrogateDiagTailX0RatChunk000Sub001Block088Part009

theorem surrogateDiagonalTailChunk000Sub001Block088Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part009] using hcert

def TailChunk000Sub001Block088Part010SupportExplicit : Finset ℕ :=
  ([11918] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part010 : ℚ :=
  (86060415709 : ℚ) / 113187592992000000

def SurrogateDiagonalTailChunk000Sub001Block088Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11918
    = surrogateDiagTailX0RatChunk000Sub001Block088Part010

theorem surrogateDiagonalTailChunk000Sub001Block088Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part010] using hcert

def TailChunk000Sub001Block088Part011SupportExplicit : Finset ℕ :=
  ([11919] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part011 : ℚ :=
  (4628000753875 : ℚ) / 8412684470313811968

def SurrogateDiagonalTailChunk000Sub001Block088Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11919
    = surrogateDiagTailX0RatChunk000Sub001Block088Part011

theorem surrogateDiagonalTailChunk000Sub001Block088Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part011] using hcert

def TailChunk000Sub001Block088Part012SupportExplicit : Finset ℕ :=
  ([11921] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part012 : ℚ :=
  (47898879017 : ℚ) / 153539542011248640

def SurrogateDiagonalTailChunk000Sub001Block088Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11921
    = surrogateDiagTailX0RatChunk000Sub001Block088Part012

theorem surrogateDiagonalTailChunk000Sub001Block088Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part012] using hcert

def TailChunk000Sub001Block088Part013SupportExplicit : Finset ℕ :=
  ([11922] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part013 : ℚ :=
  (49323275 : ℚ) / 20742242781888

def SurrogateDiagonalTailChunk000Sub001Block088Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11922
    = surrogateDiagTailX0RatChunk000Sub001Block088Part013

theorem surrogateDiagonalTailChunk000Sub001Block088Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part013] using hcert

def TailChunk000Sub001Block088Part014SupportExplicit : Finset ℕ :=
  ([11923] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part014 : ℚ :=
  (2221217640625 : ℚ) / 12628836408803724882

def SurrogateDiagonalTailChunk000Sub001Block088Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11923
    = surrogateDiagTailX0RatChunk000Sub001Block088Part014

theorem surrogateDiagonalTailChunk000Sub001Block088Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part014] using hcert

def TailChunk000Sub001Block088Part015SupportExplicit : Finset ℕ :=
  ([11926] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part015 : ℚ :=
  (2156280672325 : ℚ) / 2845334237163061248

def SurrogateDiagonalTailChunk000Sub001Block088Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11926
    = surrogateDiagTailX0RatChunk000Sub001Block088Part015

theorem surrogateDiagonalTailChunk000Sub001Block088Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part015] using hcert

def TailChunk000Sub001Block088Part016SupportExplicit : Finset ℕ :=
  ([11927] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part016 : ℚ :=
  (2222708265625 : ℚ) / 12645793555002014322

def SurrogateDiagonalTailChunk000Sub001Block088Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11927
    = surrogateDiagTailX0RatChunk000Sub001Block088Part016

theorem surrogateDiagonalTailChunk000Sub001Block088Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part016] using hcert

def TailChunk000Sub001Block088Part017SupportExplicit : Finset ℕ :=
  ([11929] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part017 : ℚ :=
  (345024990607 : ℚ) / 1874261987442000000

def SurrogateDiagonalTailChunk000Sub001Block088Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11929
    = surrogateDiagTailX0RatChunk000Sub001Block088Part017

theorem surrogateDiagonalTailChunk000Sub001Block088Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part017] using hcert

def TailChunk000Sub001Block088Part018SupportExplicit : Finset ℕ :=
  ([11930] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part018 : ℚ :=
  (844422923075 : ℚ) / 646162648767135744

def SurrogateDiagonalTailChunk000Sub001Block088Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11930
    = surrogateDiagTailX0RatChunk000Sub001Block088Part018

theorem surrogateDiagonalTailChunk000Sub001Block088Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part018] using hcert

def TailChunk000Sub001Block088Part019SupportExplicit : Finset ℕ :=
  ([11931] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part019 : ℚ :=
  (25118363713 : ℚ) / 57993654907699200

def SurrogateDiagonalTailChunk000Sub001Block088Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11931
    = surrogateDiagTailX0RatChunk000Sub001Block088Part019

theorem surrogateDiagonalTailChunk000Sub001Block088Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part019] using hcert

def TailChunk000Sub001Block088Part020SupportExplicit : Finset ℕ :=
  ([11933] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part020 : ℚ :=
  (2224945140625 : ℚ) / 12671261285911440672

def SurrogateDiagonalTailChunk000Sub001Block088Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11933
    = surrogateDiagTailX0RatChunk000Sub001Block088Part020

theorem surrogateDiagonalTailChunk000Sub001Block088Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part020] using hcert

def TailChunk000Sub001Block088Part021SupportExplicit : Finset ℕ :=
  ([11935] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part021 : ℚ :=
  (438092093 : ℚ) / 746645299200000

def SurrogateDiagonalTailChunk000Sub001Block088Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11935
    = surrogateDiagTailX0RatChunk000Sub001Block088Part021

theorem surrogateDiagonalTailChunk000Sub001Block088Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part021] using hcert

def TailChunk000Sub001Block088Part022SupportExplicit : Finset ℕ :=
  ([11937] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part022 : ℚ :=
  (335900709125 : ℚ) / 745690597920964608

def SurrogateDiagonalTailChunk000Sub001Block088Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11937
    = surrogateDiagTailX0RatChunk000Sub001Block088Part022

theorem surrogateDiagonalTailChunk000Sub001Block088Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part022] using hcert

def TailChunk000Sub001Block088Part023SupportExplicit : Finset ℕ :=
  ([11938] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part023 : ℚ :=
  (119550734525 : ℚ) / 156771769744812096

def SurrogateDiagonalTailChunk000Sub001Block088Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11938
    = surrogateDiagTailX0RatChunk000Sub001Block088Part023

theorem surrogateDiagonalTailChunk000Sub001Block088Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part023] using hcert

def TailChunk000Sub001Block088Part024SupportExplicit : Finset ℕ :=
  ([11939] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block088Part024 : ℚ :=
  (2227183140625 : ℚ) / 12696767465119089042

def SurrogateDiagonalTailChunk000Sub001Block088Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11939
    = surrogateDiagTailX0RatChunk000Sub001Block088Part024

theorem surrogateDiagonalTailChunk000Sub001Block088Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block088Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block088Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block088Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block088Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block088Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block088HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block088Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block088Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block088Part000
    + surrogateDiagTailX0RatChunk000Sub001Block088Part001
    + surrogateDiagTailX0RatChunk000Sub001Block088Part002
    + surrogateDiagTailX0RatChunk000Sub001Block088Part003
    + surrogateDiagTailX0RatChunk000Sub001Block088Part004
    + surrogateDiagTailX0RatChunk000Sub001Block088Part005
    + surrogateDiagTailX0RatChunk000Sub001Block088Part006
    + surrogateDiagTailX0RatChunk000Sub001Block088Part007
    + surrogateDiagTailX0RatChunk000Sub001Block088Part008
    + surrogateDiagTailX0RatChunk000Sub001Block088Part009

def surrogateDiagonalTailChunk000Sub001Block088MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block088Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block088Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block088Part010
    + surrogateDiagTailX0RatChunk000Sub001Block088Part011
    + surrogateDiagTailX0RatChunk000Sub001Block088Part012
    + surrogateDiagTailX0RatChunk000Sub001Block088Part013
    + surrogateDiagTailX0RatChunk000Sub001Block088Part014
    + surrogateDiagTailX0RatChunk000Sub001Block088Part015
    + surrogateDiagTailX0RatChunk000Sub001Block088Part016
    + surrogateDiagTailX0RatChunk000Sub001Block088Part017
    + surrogateDiagTailX0RatChunk000Sub001Block088Part018
    + surrogateDiagTailX0RatChunk000Sub001Block088Part019

def surrogateDiagonalTailChunk000Sub001Block088TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block088Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block088Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block088Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block088Part020
    + surrogateDiagTailX0RatChunk000Sub001Block088Part021
    + surrogateDiagTailX0RatChunk000Sub001Block088Part022
    + surrogateDiagTailX0RatChunk000Sub001Block088Part023
    + surrogateDiagTailX0RatChunk000Sub001Block088Part024

def surrogateDiagonalTailChunk000Sub001Block088Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block088HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block088MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block088TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block088 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block088Part000
    + surrogateDiagTailX0RatChunk000Sub001Block088Part001
    + surrogateDiagTailX0RatChunk000Sub001Block088Part002
    + surrogateDiagTailX0RatChunk000Sub001Block088Part003
    + surrogateDiagTailX0RatChunk000Sub001Block088Part004
    + surrogateDiagTailX0RatChunk000Sub001Block088Part005
    + surrogateDiagTailX0RatChunk000Sub001Block088Part006
    + surrogateDiagTailX0RatChunk000Sub001Block088Part007
    + surrogateDiagTailX0RatChunk000Sub001Block088Part008
    + surrogateDiagTailX0RatChunk000Sub001Block088Part009
    + surrogateDiagTailX0RatChunk000Sub001Block088Part010
    + surrogateDiagTailX0RatChunk000Sub001Block088Part011
    + surrogateDiagTailX0RatChunk000Sub001Block088Part012
    + surrogateDiagTailX0RatChunk000Sub001Block088Part013
    + surrogateDiagTailX0RatChunk000Sub001Block088Part014
    + surrogateDiagTailX0RatChunk000Sub001Block088Part015
    + surrogateDiagTailX0RatChunk000Sub001Block088Part016
    + surrogateDiagTailX0RatChunk000Sub001Block088Part017
    + surrogateDiagTailX0RatChunk000Sub001Block088Part018
    + surrogateDiagTailX0RatChunk000Sub001Block088Part019
    + surrogateDiagTailX0RatChunk000Sub001Block088Part020
    + surrogateDiagTailX0RatChunk000Sub001Block088Part021
    + surrogateDiagTailX0RatChunk000Sub001Block088Part022
    + surrogateDiagTailX0RatChunk000Sub001Block088Part023
    + surrogateDiagTailX0RatChunk000Sub001Block088Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block088_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block088Head + surrogateDiagTailX0RatChunk000Sub001Block088Mid + surrogateDiagTailX0RatChunk000Sub001Block088Tail =
      surrogateDiagTailX0RatChunk000Sub001Block088 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block088Head surrogateDiagTailX0RatChunk000Sub001Block088Mid surrogateDiagTailX0RatChunk000Sub001Block088Tail surrogateDiagTailX0RatChunk000Sub001Block088
  ring

def SurrogateDiagonalTailChunk000Sub001Block088HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block088HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block088Head

def SurrogateDiagonalTailChunk000Sub001Block088MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block088MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block088Mid

def SurrogateDiagonalTailChunk000Sub001Block088TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block088TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block088Tail

theorem surrogateDiagonalTailChunk000Sub001Block088_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block088HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block088MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block088TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block088Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block088 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block088HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block088MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block088TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block088Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block088_eq_head_add_mid_add_tail

/-- Block 089 covers tail-support indices [7225,7250) and q from 11941 to 11981. -/

def TailChunk000Sub001Block089Part000SupportExplicit : Finset ℕ :=
  ([11941] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part000 : ℚ :=
  (3564687025 : ℚ) / 20328444920968992

def SurrogateDiagonalTailChunk000Sub001Block089Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11941
    = surrogateDiagTailX0RatChunk000Sub001Block089Part000

theorem surrogateDiagonalTailChunk000Sub001Block089Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part000] using hcert

def TailChunk000Sub001Block089Part001SupportExplicit : Finset ℕ :=
  ([11942] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part001 : ℚ :=
  (1862364115975 : ℚ) / 1707616094707795968

def SurrogateDiagonalTailChunk000Sub001Block089Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11942
    = surrogateDiagTailX0RatChunk000Sub001Block089Part001

theorem surrogateDiagonalTailChunk000Sub001Block089Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part001] using hcert

def TailChunk000Sub001Block089Part002SupportExplicit : Finset ℕ :=
  ([11945] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part002 : ℚ :=
  (6060773620975 : ℚ) / 20816327599072247808

def SurrogateDiagonalTailChunk000Sub001Block089Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11945
    = surrogateDiagTailX0RatChunk000Sub001Block089Part002

theorem surrogateDiagonalTailChunk000Sub001Block089Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part002] using hcert

def TailChunk000Sub001Block089Part003SupportExplicit : Finset ℕ :=
  ([11946] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part003 : ℚ :=
  (45049794457 : ℚ) / 16799519232000000

def SurrogateDiagonalTailChunk000Sub001Block089Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11946
    = surrogateDiagTailX0RatChunk000Sub001Block089Part003

theorem surrogateDiagonalTailChunk000Sub001Block089Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part003] using hcert

def TailChunk000Sub001Block089Part004SupportExplicit : Finset ℕ :=
  ([11947] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part004 : ℚ :=
  (3899913062225 : ℚ) / 18411644137870992384

def SurrogateDiagonalTailChunk000Sub001Block089Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11947
    = surrogateDiagTailX0RatChunk000Sub001Block089Part004

theorem surrogateDiagonalTailChunk000Sub001Block089Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part004] using hcert

def TailChunk000Sub001Block089Part005SupportExplicit : Finset ℕ :=
  ([11949] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part005 : ℚ :=
  (1594747857875 : ℚ) / 2698455063241949184

def SurrogateDiagonalTailChunk000Sub001Block089Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11949
    = surrogateDiagTailX0RatChunk000Sub001Block089Part005

theorem surrogateDiagonalTailChunk000Sub001Block089Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part005] using hcert

def TailChunk000Sub001Block089Part006SupportExplicit : Finset ℕ :=
  ([11951] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part006 : ℚ :=
  (2372990276225 : ℚ) / 9631314361813303296

def SurrogateDiagonalTailChunk000Sub001Block089Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11951
    = surrogateDiagTailX0RatChunk000Sub001Block089Part006

theorem surrogateDiagonalTailChunk000Sub001Block089Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part006] using hcert

def TailChunk000Sub001Block089Part007SupportExplicit : Finset ℕ :=
  ([11953] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part007 : ℚ :=
  (2232409515625 : ℚ) / 12756431621726871552

def SurrogateDiagonalTailChunk000Sub001Block089Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11953
    = surrogateDiagTailX0RatChunk000Sub001Block089Part007

theorem surrogateDiagonalTailChunk000Sub001Block089Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part007] using hcert

def TailChunk000Sub001Block089Part008SupportExplicit : Finset ℕ :=
  ([11954] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part008 : ℚ :=
  (1077385783625 : ℚ) / 1410945927703308864

def SurrogateDiagonalTailChunk000Sub001Block089Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11954
    = surrogateDiagTailX0RatChunk000Sub001Block089Part008

theorem surrogateDiagonalTailChunk000Sub001Block089Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part008] using hcert

def TailChunk000Sub001Block089Part009SupportExplicit : Finset ℕ :=
  ([11955] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part009 : ℚ :=
  (951180791175 : ℚ) / 1370622393354551296

def SurrogateDiagonalTailChunk000Sub001Block089Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11955
    = surrogateDiagTailX0RatChunk000Sub001Block089Part009

theorem surrogateDiagonalTailChunk000Sub001Block089Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part009] using hcert

def TailChunk000Sub001Block089Part010SupportExplicit : Finset ℕ :=
  ([11957] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part010 : ℚ :=
  (306807926401 : ℚ) / 1391253119800963200

def SurrogateDiagonalTailChunk000Sub001Block089Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11957
    = surrogateDiagTailX0RatChunk000Sub001Block089Part010

theorem surrogateDiagonalTailChunk000Sub001Block089Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part010] using hcert

def TailChunk000Sub001Block089Part011SupportExplicit : Finset ℕ :=
  ([11958] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part011 : ℚ :=
  (49621625 : ℚ) / 20994042544128

def SurrogateDiagonalTailChunk000Sub001Block089Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11958
    = surrogateDiagTailX0RatChunk000Sub001Block089Part011

theorem surrogateDiagonalTailChunk000Sub001Block089Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part011] using hcert

def TailChunk000Sub001Block089Part012SupportExplicit : Finset ℕ :=
  ([11959] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part012 : ℚ :=
  (2234651265625 : ℚ) / 12782066241372670962

def SurrogateDiagonalTailChunk000Sub001Block089Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11959
    = surrogateDiagTailX0RatChunk000Sub001Block089Part012

theorem surrogateDiagonalTailChunk000Sub001Block089Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part012] using hcert

def TailChunk000Sub001Block089Part013SupportExplicit : Finset ℕ :=
  ([11962] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part013 : ℚ :=
  (894309025 : ℚ) / 1279061969401632

def SurrogateDiagonalTailChunk000Sub001Block089Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11962
    = surrogateDiagTailX0RatChunk000Sub001Block089Part013

theorem surrogateDiagonalTailChunk000Sub001Block089Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part013] using hcert

def TailChunk000Sub001Block089Part014SupportExplicit : Finset ℕ :=
  ([11963] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part014 : ℚ :=
  (247541981725 : ℚ) / 984975196935937536

def SurrogateDiagonalTailChunk000Sub001Block089Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11963
    = surrogateDiagTailX0RatChunk000Sub001Block089Part014

theorem surrogateDiagonalTailChunk000Sub001Block089Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part014] using hcert

def TailChunk000Sub001Block089Part015SupportExplicit : Finset ℕ :=
  ([11965] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part015 : ℚ :=
  (2146374551775 : ℚ) / 6985383768892112896

def SurrogateDiagonalTailChunk000Sub001Block089Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11965
    = surrogateDiagTailX0RatChunk000Sub001Block089Part015

theorem surrogateDiagonalTailChunk000Sub001Block089Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part015] using hcert

def TailChunk000Sub001Block089Part016SupportExplicit : Finset ℕ :=
  ([11966] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part016 : ℚ :=
  (1903037471 : ℚ) / 2446607316418560

def SurrogateDiagonalTailChunk000Sub001Block089Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11966
    = surrogateDiagTailX0RatChunk000Sub001Block089Part016

theorem surrogateDiagonalTailChunk000Sub001Block089Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part016] using hcert

def TailChunk000Sub001Block089Part017SupportExplicit : Finset ℕ :=
  ([11967] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part017 : ℚ :=
  (3976660601125 : ℚ) / 10119695389280421888

def SurrogateDiagonalTailChunk000Sub001Block089Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11967
    = surrogateDiagTailX0RatChunk000Sub001Block089Part017

theorem surrogateDiagonalTailChunk000Sub001Block089Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part017] using hcert

def TailChunk000Sub001Block089Part018SupportExplicit : Finset ℕ :=
  ([11969] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part018 : ℚ :=
  (2238390015625 : ℚ) / 12824876440010883072

def SurrogateDiagonalTailChunk000Sub001Block089Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11969
    = surrogateDiagTailX0RatChunk000Sub001Block089Part018

theorem surrogateDiagonalTailChunk000Sub001Block089Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part018] using hcert

def TailChunk000Sub001Block089Part019SupportExplicit : Finset ℕ :=
  ([11971] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part019 : ℚ :=
  (3582621025 : ℚ) / 20533522188070962

def SurrogateDiagonalTailChunk000Sub001Block089Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11971
    = surrogateDiagTailX0RatChunk000Sub001Block089Part019

theorem surrogateDiagonalTailChunk000Sub001Block089Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part019] using hcert

def TailChunk000Sub001Block089Part020SupportExplicit : Finset ℕ :=
  ([11973] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part020 : ℚ :=
  (3553953482725 : ℚ) / 7273735955702120448

def SurrogateDiagonalTailChunk000Sub001Block089Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11973
    = surrogateDiagTailX0RatChunk000Sub001Block089Part020

theorem surrogateDiagonalTailChunk000Sub001Block089Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part020] using hcert

def TailChunk000Sub001Block089Part021SupportExplicit : Finset ℕ :=
  ([11974] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part021 : ℚ :=
  (560065140625 : ℚ) / 802626912147782802

def SurrogateDiagonalTailChunk000Sub001Block089Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11974
    = surrogateDiagTailX0RatChunk000Sub001Block089Part021

theorem surrogateDiagonalTailChunk000Sub001Block089Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part021] using hcert

def TailChunk000Sub001Block089Part022SupportExplicit : Finset ℕ :=
  ([11977] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part022 : ℚ :=
  (3206064869675 : ℚ) / 11270572171610701824

def SurrogateDiagonalTailChunk000Sub001Block089Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11977
    = surrogateDiagTailX0RatChunk000Sub001Block089Part022

theorem surrogateDiagonalTailChunk000Sub001Block089Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part022] using hcert

def TailChunk000Sub001Block089Part023SupportExplicit : Finset ℕ :=
  ([11978] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part023 : ℚ :=
  (723682179375 : ℚ) / 958939193562628096

def SurrogateDiagonalTailChunk000Sub001Block089Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11978
    = surrogateDiagTailX0RatChunk000Sub001Block089Part023

theorem surrogateDiagonalTailChunk000Sub001Block089Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part023] using hcert

def TailChunk000Sub001Block089Part024SupportExplicit : Finset ℕ :=
  ([11981] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub001Block089Part024 : ℚ :=
  (3588609025 : ℚ) / 20602224837203232

def SurrogateDiagonalTailChunk000Sub001Block089Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 11981
    = surrogateDiagTailX0RatChunk000Sub001Block089Part024

theorem surrogateDiagonalTailChunk000Sub001Block089Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub001Block089Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub001Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub001Block089Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub001Block089Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub001Block089Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub001Block089Part024] using hcert

def surrogateDiagonalTailChunk000Sub001Block089HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block089Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block089Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block089Part000
    + surrogateDiagTailX0RatChunk000Sub001Block089Part001
    + surrogateDiagTailX0RatChunk000Sub001Block089Part002
    + surrogateDiagTailX0RatChunk000Sub001Block089Part003
    + surrogateDiagTailX0RatChunk000Sub001Block089Part004
    + surrogateDiagTailX0RatChunk000Sub001Block089Part005
    + surrogateDiagTailX0RatChunk000Sub001Block089Part006
    + surrogateDiagTailX0RatChunk000Sub001Block089Part007
    + surrogateDiagTailX0RatChunk000Sub001Block089Part008
    + surrogateDiagTailX0RatChunk000Sub001Block089Part009

def surrogateDiagonalTailChunk000Sub001Block089MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block089Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block089Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block089Part010
    + surrogateDiagTailX0RatChunk000Sub001Block089Part011
    + surrogateDiagTailX0RatChunk000Sub001Block089Part012
    + surrogateDiagTailX0RatChunk000Sub001Block089Part013
    + surrogateDiagTailX0RatChunk000Sub001Block089Part014
    + surrogateDiagTailX0RatChunk000Sub001Block089Part015
    + surrogateDiagTailX0RatChunk000Sub001Block089Part016
    + surrogateDiagTailX0RatChunk000Sub001Block089Part017
    + surrogateDiagTailX0RatChunk000Sub001Block089Part018
    + surrogateDiagTailX0RatChunk000Sub001Block089Part019

def surrogateDiagonalTailChunk000Sub001Block089TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub001Block089Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub001Block089Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub001Block089Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block089Part020
    + surrogateDiagTailX0RatChunk000Sub001Block089Part021
    + surrogateDiagTailX0RatChunk000Sub001Block089Part022
    + surrogateDiagTailX0RatChunk000Sub001Block089Part023
    + surrogateDiagTailX0RatChunk000Sub001Block089Part024

def surrogateDiagonalTailChunk000Sub001Block089Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub001Block089HeadSum X0
    + surrogateDiagonalTailChunk000Sub001Block089MidSum X0
    + surrogateDiagonalTailChunk000Sub001Block089TailSum X0

def surrogateDiagTailX0RatChunk000Sub001Block089 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub001Block089Part000
    + surrogateDiagTailX0RatChunk000Sub001Block089Part001
    + surrogateDiagTailX0RatChunk000Sub001Block089Part002
    + surrogateDiagTailX0RatChunk000Sub001Block089Part003
    + surrogateDiagTailX0RatChunk000Sub001Block089Part004
    + surrogateDiagTailX0RatChunk000Sub001Block089Part005
    + surrogateDiagTailX0RatChunk000Sub001Block089Part006
    + surrogateDiagTailX0RatChunk000Sub001Block089Part007
    + surrogateDiagTailX0RatChunk000Sub001Block089Part008
    + surrogateDiagTailX0RatChunk000Sub001Block089Part009
    + surrogateDiagTailX0RatChunk000Sub001Block089Part010
    + surrogateDiagTailX0RatChunk000Sub001Block089Part011
    + surrogateDiagTailX0RatChunk000Sub001Block089Part012
    + surrogateDiagTailX0RatChunk000Sub001Block089Part013
    + surrogateDiagTailX0RatChunk000Sub001Block089Part014
    + surrogateDiagTailX0RatChunk000Sub001Block089Part015
    + surrogateDiagTailX0RatChunk000Sub001Block089Part016
    + surrogateDiagTailX0RatChunk000Sub001Block089Part017
    + surrogateDiagTailX0RatChunk000Sub001Block089Part018
    + surrogateDiagTailX0RatChunk000Sub001Block089Part019
    + surrogateDiagTailX0RatChunk000Sub001Block089Part020
    + surrogateDiagTailX0RatChunk000Sub001Block089Part021
    + surrogateDiagTailX0RatChunk000Sub001Block089Part022
    + surrogateDiagTailX0RatChunk000Sub001Block089Part023
    + surrogateDiagTailX0RatChunk000Sub001Block089Part024

theorem surrogateDiagTailX0RatChunk000Sub001Block089_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub001Block089Head + surrogateDiagTailX0RatChunk000Sub001Block089Mid + surrogateDiagTailX0RatChunk000Sub001Block089Tail =
      surrogateDiagTailX0RatChunk000Sub001Block089 := by
  unfold surrogateDiagTailX0RatChunk000Sub001Block089Head surrogateDiagTailX0RatChunk000Sub001Block089Mid surrogateDiagTailX0RatChunk000Sub001Block089Tail surrogateDiagTailX0RatChunk000Sub001Block089
  ring

def SurrogateDiagonalTailChunk000Sub001Block089HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block089HeadSum X0 = surrogateDiagTailX0RatChunk000Sub001Block089Head

def SurrogateDiagonalTailChunk000Sub001Block089MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block089MidSum X0 = surrogateDiagTailX0RatChunk000Sub001Block089Mid

def SurrogateDiagonalTailChunk000Sub001Block089TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub001Block089TailSum X0 = surrogateDiagTailX0RatChunk000Sub001Block089Tail

theorem surrogateDiagonalTailChunk000Sub001Block089_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub001Block089HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub001Block089MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub001Block089TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub001Block089Sum X0 = surrogateDiagTailX0RatChunk000Sub001Block089 := by
  unfold SurrogateDiagonalTailChunk000Sub001Block089HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub001Block089MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub001Block089TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub001Block089Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub001Block089_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
