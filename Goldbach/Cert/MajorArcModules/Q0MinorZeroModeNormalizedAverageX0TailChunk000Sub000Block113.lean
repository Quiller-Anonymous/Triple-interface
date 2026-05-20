import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [113,114). -/

/- Block 113 covers tail-support indices [2825,2850) and q from 4697 to 4735. -/

def TailChunk000Sub000Block113Part000SupportExplicit : Finset ℕ :=
  ([4697] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part000 : ℚ :=
  (5335941311 : ℚ) / 2099939904000000

def SurrogateDiagonalTailChunk000Sub000Block113Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4697
    = surrogateDiagTailX0RatChunk000Sub000Block113Part000

theorem surrogateDiagonalTailChunk000Sub000Block113Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part000] using hcert

def TailChunk000Sub000Block113Part001SupportExplicit : Finset ℕ :=
  ([4699] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part001 : ℚ :=
  (667541722325 : ℚ) / 529284342560891904

def SurrogateDiagonalTailChunk000Sub000Block113Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4699
    = surrogateDiagTailX0RatChunk000Sub000Block113Part001

theorem surrogateDiagonalTailChunk000Sub000Block113Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part001] using hcert

def TailChunk000Sub000Block113Part002SupportExplicit : Finset ℕ :=
  ([4701] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part002 : ℚ :=
  (30675275 : ℚ) / 8018733267648

def SurrogateDiagonalTailChunk000Sub000Block113Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4701
    = surrogateDiagTailX0RatChunk000Sub000Block113Part002

theorem surrogateDiagonalTailChunk000Sub000Block113Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part002] using hcert

def TailChunk000Sub000Block113Part003SupportExplicit : Finset ℕ :=
  ([4702] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part003 : ℚ :=
  (27630477799 : ℚ) / 3050410585125000

def SurrogateDiagonalTailChunk000Sub000Block113Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4702
    = surrogateDiagTailX0RatChunk000Sub000Block113Part003

theorem surrogateDiagonalTailChunk000Sub000Block113Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part003] using hcert

def TailChunk000Sub000Block113Part004SupportExplicit : Finset ℕ :=
  ([4703] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part004 : ℚ :=
  (345597015625 : ℚ) / 305560608845798802

def SurrogateDiagonalTailChunk000Sub000Block113Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4703
    = surrogateDiagTailX0RatChunk000Sub000Block113Part004

theorem surrogateDiagonalTailChunk000Sub000Block113Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part004] using hcert

def TailChunk000Sub000Block113Part005SupportExplicit : Finset ℕ :=
  ([4705] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part005 : ℚ :=
  (4423883599 : ℚ) / 1999117081067520

def SurrogateDiagonalTailChunk000Sub000Block113Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4705
    = surrogateDiagTailX0RatChunk000Sub000Block113Part005

theorem surrogateDiagonalTailChunk000Sub000Block113Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part005] using hcert

def TailChunk000Sub000Block113Part006SupportExplicit : Finset ℕ :=
  ([4706] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part006 : ℚ :=
  (2843156077 : ℚ) / 241913076940800

def SurrogateDiagonalTailChunk000Sub000Block113Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4706
    = surrogateDiagTailX0RatChunk000Sub000Block113Part006

theorem surrogateDiagonalTailChunk000Sub000Block113Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part006] using hcert

def TailChunk000Sub000Block113Part007SupportExplicit : Finset ℕ :=
  ([4709] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part007 : ℚ :=
  (1304994133375 : ℚ) / 950918108380397568

def SurrogateDiagonalTailChunk000Sub000Block113Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4709
    = surrogateDiagTailX0RatChunk000Sub000Block113Part007

theorem surrogateDiagonalTailChunk000Sub000Block113Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part007] using hcert

def TailChunk000Sub000Block113Part008SupportExplicit : Finset ℕ :=
  ([4710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part008 : ℚ :=
  (398012605975 : ℚ) / 6065759684395008

def SurrogateDiagonalTailChunk000Sub000Block113Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4710
    = surrogateDiagTailX0RatChunk000Sub000Block113Part008

theorem surrogateDiagonalTailChunk000Sub000Block113Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part008] using hcert

def TailChunk000Sub000Block113Part009SupportExplicit : Finset ℕ :=
  ([4711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part009 : ℚ :=
  (303935309875 : ℚ) / 165214804689027072

def SurrogateDiagonalTailChunk000Sub000Block113Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4711
    = surrogateDiagTailX0RatChunk000Sub000Block113Part009

theorem surrogateDiagonalTailChunk000Sub000Block113Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part009] using hcert

def TailChunk000Sub000Block113Part010SupportExplicit : Finset ℕ :=
  ([4713] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part010 : ℚ :=
  (3699849 : ℚ) / 972117121600

def SurrogateDiagonalTailChunk000Sub000Block113Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4713
    = surrogateDiagTailX0RatChunk000Sub000Block113Part010

theorem surrogateDiagonalTailChunk000Sub000Block113Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part010] using hcert

def TailChunk000Sub000Block113Part011SupportExplicit : Finset ℕ :=
  ([4714] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part011 : ℚ :=
  (694292238775 : ℚ) / 77042080689310848

def SurrogateDiagonalTailChunk000Sub000Block113Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4714
    = surrogateDiagTailX0RatChunk000Sub000Block113Part011

theorem surrogateDiagonalTailChunk000Sub000Block113Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part011] using hcert

def TailChunk000Sub000Block113Part012SupportExplicit : Finset ℕ :=
  ([4715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part012 : ℚ :=
  (2603749543 : ℚ) / 959704478515200

def SurrogateDiagonalTailChunk000Sub000Block113Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4715
    = surrogateDiagTailX0RatChunk000Sub000Block113Part012

theorem surrogateDiagonalTailChunk000Sub000Block113Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part012] using hcert

def TailChunk000Sub000Block113Part013SupportExplicit : Finset ℕ :=
  ([4717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part013 : ℚ :=
  (2660410173325 : ℚ) / 1096404784434905088

def SurrogateDiagonalTailChunk000Sub000Block113Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4717
    = surrogateDiagTailX0RatChunk000Sub000Block113Part013

theorem surrogateDiagonalTailChunk000Sub000Block113Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part013] using hcert

def TailChunk000Sub000Block113Part014SupportExplicit : Finset ℕ :=
  ([4718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part014 : ℚ :=
  (31433533225 : ℚ) / 1529766710083584

def SurrogateDiagonalTailChunk000Sub000Block113Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4718
    = surrogateDiagTailX0RatChunk000Sub000Block113Part014

theorem surrogateDiagonalTailChunk000Sub000Block113Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part014] using hcert

def TailChunk000Sub000Block113Part015SupportExplicit : Finset ℕ :=
  ([4721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part015 : ℚ :=
  (557196025 : ℚ) / 496426371981312

def SurrogateDiagonalTailChunk000Sub000Block113Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4721
    = surrogateDiagTailX0RatChunk000Sub000Block113Part015

theorem surrogateDiagonalTailChunk000Sub000Block113Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part015] using hcert

def TailChunk000Sub000Block113Part016SupportExplicit : Finset ℕ :=
  ([4722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part016 : ℚ :=
  (3436825 : ℚ) / 113087969664

def SurrogateDiagonalTailChunk000Sub000Block113Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4722
    = surrogateDiagTailX0RatChunk000Sub000Block113Part016

theorem surrogateDiagonalTailChunk000Sub000Block113Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part016] using hcert

def TailChunk000Sub000Block113Part017SupportExplicit : Finset ℕ :=
  ([4723] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part017 : ℚ :=
  (348542640625 : ℚ) / 310792692219632082

def SurrogateDiagonalTailChunk000Sub000Block113Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4723
    = surrogateDiagTailX0RatChunk000Sub000Block113Part017

theorem surrogateDiagonalTailChunk000Sub000Block113Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part017] using hcert

def TailChunk000Sub000Block113Part018SupportExplicit : Finset ℕ :=
  ([4726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part018 : ℚ :=
  (163742646325 : ℚ) / 14858095443443712

def SurrogateDiagonalTailChunk000Sub000Block113Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4726
    = surrogateDiagTailX0RatChunk000Sub000Block113Part018

theorem surrogateDiagonalTailChunk000Sub000Block113Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part018] using hcert

def TailChunk000Sub000Block113Part019SupportExplicit : Finset ℕ :=
  ([4727] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part019 : ℚ :=
  (192015711625 : ℚ) / 151224097874540544

def SurrogateDiagonalTailChunk000Sub000Block113Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4727
    = surrogateDiagTailX0RatChunk000Sub000Block113Part019

theorem surrogateDiagonalTailChunk000Sub000Block113Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part019] using hcert

def TailChunk000Sub000Block113Part020SupportExplicit : Finset ℕ :=
  ([4729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part020 : ℚ :=
  (349428765625 : ℚ) / 312375337995244032

def SurrogateDiagonalTailChunk000Sub000Block113Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4729
    = surrogateDiagTailX0RatChunk000Sub000Block113Part020

theorem surrogateDiagonalTailChunk000Sub000Block113Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part020] using hcert

def TailChunk000Sub000Block113Part021SupportExplicit : Finset ℕ :=
  ([4730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part021 : ℚ :=
  (317372207 : ℚ) / 12646880870400

def SurrogateDiagonalTailChunk000Sub000Block113Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4730
    = surrogateDiagTailX0RatChunk000Sub000Block113Part021

theorem surrogateDiagonalTailChunk000Sub000Block113Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part021] using hcert

def TailChunk000Sub000Block113Part022SupportExplicit : Finset ℕ :=
  ([4731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part022 : ℚ :=
  (438092504975 : ℚ) / 94942852529071104

def SurrogateDiagonalTailChunk000Sub000Block113Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4731
    = surrogateDiagTailX0RatChunk000Sub000Block113Part022

theorem surrogateDiagonalTailChunk000Sub000Block113Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part022] using hcert

def TailChunk000Sub000Block113Part023SupportExplicit : Finset ℕ :=
  ([4733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part023 : ℚ :=
  (350020140625 : ℚ) / 313433788002115872

def SurrogateDiagonalTailChunk000Sub000Block113Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4733
    = surrogateDiagTailX0RatChunk000Sub000Block113Part023

theorem surrogateDiagonalTailChunk000Sub000Block113Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part023] using hcert

def TailChunk000Sub000Block113Part024SupportExplicit : Finset ℕ :=
  ([4735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block113Part024 : ℚ :=
  (392016932625 : ℚ) / 170887428690221056

def SurrogateDiagonalTailChunk000Sub000Block113Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 4735
    = surrogateDiagTailX0RatChunk000Sub000Block113Part024

theorem surrogateDiagonalTailChunk000Sub000Block113Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block113Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block113Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block113Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block113Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block113Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block113HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block113Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block113Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block113Part000
    + surrogateDiagTailX0RatChunk000Sub000Block113Part001
    + surrogateDiagTailX0RatChunk000Sub000Block113Part002
    + surrogateDiagTailX0RatChunk000Sub000Block113Part003
    + surrogateDiagTailX0RatChunk000Sub000Block113Part004
    + surrogateDiagTailX0RatChunk000Sub000Block113Part005
    + surrogateDiagTailX0RatChunk000Sub000Block113Part006
    + surrogateDiagTailX0RatChunk000Sub000Block113Part007
    + surrogateDiagTailX0RatChunk000Sub000Block113Part008
    + surrogateDiagTailX0RatChunk000Sub000Block113Part009

def surrogateDiagonalTailChunk000Sub000Block113MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block113Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block113Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block113Part010
    + surrogateDiagTailX0RatChunk000Sub000Block113Part011
    + surrogateDiagTailX0RatChunk000Sub000Block113Part012
    + surrogateDiagTailX0RatChunk000Sub000Block113Part013
    + surrogateDiagTailX0RatChunk000Sub000Block113Part014
    + surrogateDiagTailX0RatChunk000Sub000Block113Part015
    + surrogateDiagTailX0RatChunk000Sub000Block113Part016
    + surrogateDiagTailX0RatChunk000Sub000Block113Part017
    + surrogateDiagTailX0RatChunk000Sub000Block113Part018
    + surrogateDiagTailX0RatChunk000Sub000Block113Part019

def surrogateDiagonalTailChunk000Sub000Block113TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block113Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block113Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block113Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block113Part020
    + surrogateDiagTailX0RatChunk000Sub000Block113Part021
    + surrogateDiagTailX0RatChunk000Sub000Block113Part022
    + surrogateDiagTailX0RatChunk000Sub000Block113Part023
    + surrogateDiagTailX0RatChunk000Sub000Block113Part024

def surrogateDiagonalTailChunk000Sub000Block113Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block113HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block113MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block113TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block113 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block113Part000
    + surrogateDiagTailX0RatChunk000Sub000Block113Part001
    + surrogateDiagTailX0RatChunk000Sub000Block113Part002
    + surrogateDiagTailX0RatChunk000Sub000Block113Part003
    + surrogateDiagTailX0RatChunk000Sub000Block113Part004
    + surrogateDiagTailX0RatChunk000Sub000Block113Part005
    + surrogateDiagTailX0RatChunk000Sub000Block113Part006
    + surrogateDiagTailX0RatChunk000Sub000Block113Part007
    + surrogateDiagTailX0RatChunk000Sub000Block113Part008
    + surrogateDiagTailX0RatChunk000Sub000Block113Part009
    + surrogateDiagTailX0RatChunk000Sub000Block113Part010
    + surrogateDiagTailX0RatChunk000Sub000Block113Part011
    + surrogateDiagTailX0RatChunk000Sub000Block113Part012
    + surrogateDiagTailX0RatChunk000Sub000Block113Part013
    + surrogateDiagTailX0RatChunk000Sub000Block113Part014
    + surrogateDiagTailX0RatChunk000Sub000Block113Part015
    + surrogateDiagTailX0RatChunk000Sub000Block113Part016
    + surrogateDiagTailX0RatChunk000Sub000Block113Part017
    + surrogateDiagTailX0RatChunk000Sub000Block113Part018
    + surrogateDiagTailX0RatChunk000Sub000Block113Part019
    + surrogateDiagTailX0RatChunk000Sub000Block113Part020
    + surrogateDiagTailX0RatChunk000Sub000Block113Part021
    + surrogateDiagTailX0RatChunk000Sub000Block113Part022
    + surrogateDiagTailX0RatChunk000Sub000Block113Part023
    + surrogateDiagTailX0RatChunk000Sub000Block113Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block113_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block113Head + surrogateDiagTailX0RatChunk000Sub000Block113Mid + surrogateDiagTailX0RatChunk000Sub000Block113Tail =
      surrogateDiagTailX0RatChunk000Sub000Block113 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block113Head surrogateDiagTailX0RatChunk000Sub000Block113Mid surrogateDiagTailX0RatChunk000Sub000Block113Tail surrogateDiagTailX0RatChunk000Sub000Block113
  ring

def SurrogateDiagonalTailChunk000Sub000Block113HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block113HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block113Head

def SurrogateDiagonalTailChunk000Sub000Block113MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block113MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block113Mid

def SurrogateDiagonalTailChunk000Sub000Block113TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block113TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block113Tail

theorem surrogateDiagonalTailChunk000Sub000Block113_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block113HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block113MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block113TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block113Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block113 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block113HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block113MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block113TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block113Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block113_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
