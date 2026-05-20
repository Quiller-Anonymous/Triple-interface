import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [164,165). -/

/-- Block 164 covers tail-support indices [4100,4125) and q from 6793 to 6833. -/

def TailChunk000Sub000Block164Part000SupportExplicit : Finset ℕ :=
  ([6793] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part000 : ℚ :=
  (721013265625 : ℚ) / 1330324460588339712

def SurrogateDiagonalTailChunk000Sub000Block164Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6793
    = surrogateDiagTailX0RatChunk000Sub000Block164Part000

theorem surrogateDiagonalTailChunk000Sub000Block164Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part000] using hcert

def TailChunk000Sub000Block164Part001SupportExplicit : Finset ℕ :=
  ([6794] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part001 : ℚ :=
  (707535959125 : ℚ) / 288006594038287488

def SurrogateDiagonalTailChunk000Sub000Block164Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6794
    = surrogateDiagTailX0RatChunk000Sub000Block164Part001

theorem surrogateDiagonalTailChunk000Sub000Block164Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part001] using hcert

def TailChunk000Sub000Block164Part002SupportExplicit : Finset ℕ :=
  ([6797] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part002 : ℚ :=
  (96535954087 : ℚ) / 114756894965635200

def SurrogateDiagonalTailChunk000Sub000Block164Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6797
    = surrogateDiagTailX0RatChunk000Sub000Block164Part002

theorem surrogateDiagonalTailChunk000Sub000Block164Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part002] using hcert

def TailChunk000Sub000Block164Part003SupportExplicit : Finset ℕ :=
  ([6798] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part003 : ℚ :=
  (20773894711 : ℚ) / 1732237834291200

def SurrogateDiagonalTailChunk000Sub000Block164Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6798
    = surrogateDiagTailX0RatChunk000Sub000Block164Part003

theorem surrogateDiagonalTailChunk000Sub000Block164Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part003] using hcert

def TailChunk000Sub000Block164Part004SupportExplicit : Finset ℕ :=
  ([6799] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part004 : ℚ :=
  (6001865675 : ℚ) / 8911485571446144

def SurrogateDiagonalTailChunk000Sub000Block164Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6799
    = surrogateDiagTailX0RatChunk000Sub000Block164Part004

theorem surrogateDiagonalTailChunk000Sub000Block164Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part004] using hcert

def TailChunk000Sub000Block164Part005SupportExplicit : Finset ℕ :=
  ([6801] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part005 : ℚ :=
  (200686608575 : ℚ) / 131854961616859536

def SurrogateDiagonalTailChunk000Sub000Block164Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6801
    = surrogateDiagTailX0RatChunk000Sub000Block164Part005

theorem surrogateDiagonalTailChunk000Sub000Block164Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part005] using hcert

def TailChunk000Sub000Block164Part006SupportExplicit : Finset ℕ :=
  ([6802] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part006 : ℚ :=
  (700775540425 : ℚ) / 263509871084569728

def SurrogateDiagonalTailChunk000Sub000Block164Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6802
    = surrogateDiagTailX0RatChunk000Sub000Block164Part006

theorem surrogateDiagonalTailChunk000Sub000Block164Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part006] using hcert

def TailChunk000Sub000Block164Part007SupportExplicit : Finset ℕ :=
  ([6803] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part007 : ℚ :=
  (723137640625 : ℚ) / 1338176435506757202

def SurrogateDiagonalTailChunk000Sub000Block164Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6803
    = surrogateDiagTailX0RatChunk000Sub000Block164Part007

theorem surrogateDiagonalTailChunk000Sub000Block164Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part007] using hcert

def TailChunk000Sub000Block164Part008SupportExplicit : Finset ℕ :=
  ([6805] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part008 : ℚ :=
  (43961326487 : ℚ) / 43797815859609600

def SurrogateDiagonalTailChunk000Sub000Block164Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6805
    = surrogateDiagTailX0RatChunk000Sub000Block164Part008

theorem surrogateDiagonalTailChunk000Sub000Block164Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part008] using hcert

def TailChunk000Sub000Block164Part009SupportExplicit : Finset ℕ :=
  ([6806] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part009 : ℚ :=
  (27634209497 : ℚ) / 5788315959705600

def SurrogateDiagonalTailChunk000Sub000Block164Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6806
    = surrogateDiagTailX0RatChunk000Sub000Block164Part009

theorem surrogateDiagonalTailChunk000Sub000Block164Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part009] using hcert

def TailChunk000Sub000Block164Part010SupportExplicit : Finset ℕ :=
  ([6807] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part010 : ℚ :=
  (804163535975 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub000Block164Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6807
    = surrogateDiagTailX0RatChunk000Sub000Block164Part010

theorem surrogateDiagonalTailChunk000Sub000Block164Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part010] using hcert

def TailChunk000Sub000Block164Part011SupportExplicit : Finset ℕ :=
  ([6809] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part011 : ℚ :=
  (102308258599 : ℚ) / 145895114964355200

def SurrogateDiagonalTailChunk000Sub000Block164Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6809
    = surrogateDiagTailX0RatChunk000Sub000Block164Part011

theorem surrogateDiagonalTailChunk000Sub000Block164Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part011] using hcert

def TailChunk000Sub000Block164Part012SupportExplicit : Finset ℕ :=
  ([6810] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part012 : ℚ :=
  (309318733925 : ℚ) / 13359511181082624

def SurrogateDiagonalTailChunk000Sub000Block164Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6810
    = surrogateDiagTailX0RatChunk000Sub000Block164Part012

theorem surrogateDiagonalTailChunk000Sub000Block164Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part012] using hcert

def TailChunk000Sub000Block164Part013SupportExplicit : Finset ℕ :=
  ([6814] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part013 : ℚ :=
  (1450665933775 : ℚ) / 336515779445189448

def SurrogateDiagonalTailChunk000Sub000Block164Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6814
    = surrogateDiagTailX0RatChunk000Sub000Block164Part013

theorem surrogateDiagonalTailChunk000Sub000Block164Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part013] using hcert

def TailChunk000Sub000Block164Part014SupportExplicit : Finset ℕ :=
  ([6815] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part014 : ℚ :=
  (1028607515675 : ℚ) / 880846596536008704

def SurrogateDiagonalTailChunk000Sub000Block164Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6815
    = surrogateDiagTailX0RatChunk000Sub000Block164Part014

theorem surrogateDiagonalTailChunk000Sub000Block164Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part014] using hcert

def TailChunk000Sub000Block164Part015SupportExplicit : Finset ℕ :=
  ([6817] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part015 : ℚ :=
  (107419446127 : ℚ) / 167805714432000000

def SurrogateDiagonalTailChunk000Sub000Block164Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6817
    = surrogateDiagTailX0RatChunk000Sub000Block164Part015

theorem surrogateDiagonalTailChunk000Sub000Block164Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part015] using hcert

def TailChunk000Sub000Block164Part016SupportExplicit : Finset ℕ :=
  ([6818] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part016 : ℚ :=
  (1183038427375 : ℚ) / 180791054328509568

def SurrogateDiagonalTailChunk000Sub000Block164Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6818
    = surrogateDiagTailX0RatChunk000Sub000Block164Part016

theorem surrogateDiagonalTailChunk000Sub000Block164Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part016] using hcert

def TailChunk000Sub000Block164Part017SupportExplicit : Finset ℕ :=
  ([6819] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part017 : ℚ :=
  (193636875 : ℚ) / 106584315265024

def SurrogateDiagonalTailChunk000Sub000Block164Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6819
    = surrogateDiagTailX0RatChunk000Sub000Block164Part017

theorem surrogateDiagonalTailChunk000Sub000Block164Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part017] using hcert

def TailChunk000Sub000Block164Part018SupportExplicit : Finset ℕ :=
  ([6821] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part018 : ℚ :=
  (676388904625 : ℚ) / 1077926117001537312

def SurrogateDiagonalTailChunk000Sub000Block164Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6821
    = surrogateDiagTailX0RatChunk000Sub000Block164Part018

theorem surrogateDiagonalTailChunk000Sub000Block164Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part018] using hcert

def TailChunk000Sub000Block164Part019SupportExplicit : Finset ℕ :=
  ([6823] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part019 : ℚ :=
  (727395765625 : ℚ) / 1353984609535762482

def SurrogateDiagonalTailChunk000Sub000Block164Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6823
    = surrogateDiagTailX0RatChunk000Sub000Block164Part019

theorem surrogateDiagonalTailChunk000Sub000Block164Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part019] using hcert

def TailChunk000Sub000Block164Part020SupportExplicit : Finset ℕ :=
  ([6826] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part020 : ℚ :=
  (182008890625 : ℚ) / 84723318376380192

def SurrogateDiagonalTailChunk000Sub000Block164Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6826
    = surrogateDiagTailX0RatChunk000Sub000Block164Part020

theorem surrogateDiagonalTailChunk000Sub000Block164Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part020] using hcert

def TailChunk000Sub000Block164Part021SupportExplicit : Finset ℕ :=
  ([6827] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part021 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block164Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6827
    = surrogateDiagTailX0RatChunk000Sub000Block164Part021

theorem surrogateDiagonalTailChunk000Sub000Block164Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part021] using hcert

def TailChunk000Sub000Block164Part022SupportExplicit : Finset ℕ :=
  ([6829] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part022 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block164Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6829
    = surrogateDiagTailX0RatChunk000Sub000Block164Part022

theorem surrogateDiagonalTailChunk000Sub000Block164Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part022] using hcert

def TailChunk000Sub000Block164Part023SupportExplicit : Finset ℕ :=
  ([6830] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part023 : ℚ :=
  (640899822775 : ℚ) / 138485506203568128

def SurrogateDiagonalTailChunk000Sub000Block164Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6830
    = surrogateDiagTailX0RatChunk000Sub000Block164Part023

theorem surrogateDiagonalTailChunk000Sub000Block164Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part023] using hcert

def TailChunk000Sub000Block164Part024SupportExplicit : Finset ℕ :=
  ([6833] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block164Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block164Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6833
    = surrogateDiagTailX0RatChunk000Sub000Block164Part024

theorem surrogateDiagonalTailChunk000Sub000Block164Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block164Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block164Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block164Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block164Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block164Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block164HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block164Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block164Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part000
    + surrogateDiagTailX0RatChunk000Sub000Block164Part001
    + surrogateDiagTailX0RatChunk000Sub000Block164Part002
    + surrogateDiagTailX0RatChunk000Sub000Block164Part003
    + surrogateDiagTailX0RatChunk000Sub000Block164Part004
    + surrogateDiagTailX0RatChunk000Sub000Block164Part005
    + surrogateDiagTailX0RatChunk000Sub000Block164Part006
    + surrogateDiagTailX0RatChunk000Sub000Block164Part007
    + surrogateDiagTailX0RatChunk000Sub000Block164Part008
    + surrogateDiagTailX0RatChunk000Sub000Block164Part009

def surrogateDiagonalTailChunk000Sub000Block164MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block164Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block164Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part010
    + surrogateDiagTailX0RatChunk000Sub000Block164Part011
    + surrogateDiagTailX0RatChunk000Sub000Block164Part012
    + surrogateDiagTailX0RatChunk000Sub000Block164Part013
    + surrogateDiagTailX0RatChunk000Sub000Block164Part014
    + surrogateDiagTailX0RatChunk000Sub000Block164Part015
    + surrogateDiagTailX0RatChunk000Sub000Block164Part016
    + surrogateDiagTailX0RatChunk000Sub000Block164Part017
    + surrogateDiagTailX0RatChunk000Sub000Block164Part018
    + surrogateDiagTailX0RatChunk000Sub000Block164Part019

def surrogateDiagonalTailChunk000Sub000Block164TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block164Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block164Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block164Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part020
    + surrogateDiagTailX0RatChunk000Sub000Block164Part021
    + surrogateDiagTailX0RatChunk000Sub000Block164Part022
    + surrogateDiagTailX0RatChunk000Sub000Block164Part023
    + surrogateDiagTailX0RatChunk000Sub000Block164Part024

def surrogateDiagonalTailChunk000Sub000Block164Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block164HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block164MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block164TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block164 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block164Part000
    + surrogateDiagTailX0RatChunk000Sub000Block164Part001
    + surrogateDiagTailX0RatChunk000Sub000Block164Part002
    + surrogateDiagTailX0RatChunk000Sub000Block164Part003
    + surrogateDiagTailX0RatChunk000Sub000Block164Part004
    + surrogateDiagTailX0RatChunk000Sub000Block164Part005
    + surrogateDiagTailX0RatChunk000Sub000Block164Part006
    + surrogateDiagTailX0RatChunk000Sub000Block164Part007
    + surrogateDiagTailX0RatChunk000Sub000Block164Part008
    + surrogateDiagTailX0RatChunk000Sub000Block164Part009
    + surrogateDiagTailX0RatChunk000Sub000Block164Part010
    + surrogateDiagTailX0RatChunk000Sub000Block164Part011
    + surrogateDiagTailX0RatChunk000Sub000Block164Part012
    + surrogateDiagTailX0RatChunk000Sub000Block164Part013
    + surrogateDiagTailX0RatChunk000Sub000Block164Part014
    + surrogateDiagTailX0RatChunk000Sub000Block164Part015
    + surrogateDiagTailX0RatChunk000Sub000Block164Part016
    + surrogateDiagTailX0RatChunk000Sub000Block164Part017
    + surrogateDiagTailX0RatChunk000Sub000Block164Part018
    + surrogateDiagTailX0RatChunk000Sub000Block164Part019
    + surrogateDiagTailX0RatChunk000Sub000Block164Part020
    + surrogateDiagTailX0RatChunk000Sub000Block164Part021
    + surrogateDiagTailX0RatChunk000Sub000Block164Part022
    + surrogateDiagTailX0RatChunk000Sub000Block164Part023
    + surrogateDiagTailX0RatChunk000Sub000Block164Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block164_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block164Head + surrogateDiagTailX0RatChunk000Sub000Block164Mid + surrogateDiagTailX0RatChunk000Sub000Block164Tail =
      surrogateDiagTailX0RatChunk000Sub000Block164 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block164Head surrogateDiagTailX0RatChunk000Sub000Block164Mid surrogateDiagTailX0RatChunk000Sub000Block164Tail surrogateDiagTailX0RatChunk000Sub000Block164
  ring

def SurrogateDiagonalTailChunk000Sub000Block164HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block164HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block164Head

def SurrogateDiagonalTailChunk000Sub000Block164MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block164MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block164Mid

def SurrogateDiagonalTailChunk000Sub000Block164TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block164TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block164Tail

theorem surrogateDiagonalTailChunk000Sub000Block164_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block164HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block164MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block164TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block164Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block164 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block164HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block164MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block164TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block164Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block164_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
