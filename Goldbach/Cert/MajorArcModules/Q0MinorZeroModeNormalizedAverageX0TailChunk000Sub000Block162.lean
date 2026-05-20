import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [162,163). -/

/-- Block 162 covers tail-support indices [4050,4075) and q from 6710 to 6751. -/

def TailChunk000Sub000Block162Part000SupportExplicit : Finset ℕ :=
  ([6710] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part000 : ℚ :=
  (71869061 : ℚ) / 10370073600000

def SurrogateDiagonalTailChunk000Sub000Block162Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6710
    = surrogateDiagTailX0RatChunk000Sub000Block162Part000

theorem surrogateDiagonalTailChunk000Sub000Block162Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part000] using hcert

def TailChunk000Sub000Block162Part001SupportExplicit : Finset ℕ :=
  ([6711] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part001 : ℚ :=
  (781639933175 : ℚ) / 500039189688689664

def SurrogateDiagonalTailChunk000Sub000Block162Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6711
    = surrogateDiagTailX0RatChunk000Sub000Block162Part001

theorem surrogateDiagonalTailChunk000Sub000Block162Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part001] using hcert

def TailChunk000Sub000Block162Part002SupportExplicit : Finset ℕ :=
  ([6715] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part002 : ℚ :=
  (1960512982825 : ℚ) / 1552834479205122048

def SurrogateDiagonalTailChunk000Sub000Block162Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6715
    = surrogateDiagTailX0RatChunk000Sub000Block162Part002

theorem surrogateDiagonalTailChunk000Sub000Block162Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part002] using hcert

def TailChunk000Sub000Block162Part003SupportExplicit : Finset ℕ :=
  ([6717] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part003 : ℚ :=
  (391519140925 : ℚ) / 250915320216797472

def SurrogateDiagonalTailChunk000Sub000Block162Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6717
    = surrogateDiagTailX0RatChunk000Sub000Block162Part003

theorem surrogateDiagonalTailChunk000Sub000Block162Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part003] using hcert

def TailChunk000Sub000Block162Part004SupportExplicit : Finset ℕ :=
  ([6718] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part004 : ℚ :=
  (1410078052975 : ℚ) / 317943262324517448

def SurrogateDiagonalTailChunk000Sub000Block162Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6718
    = surrogateDiagTailX0RatChunk000Sub000Block162Part004

theorem surrogateDiagonalTailChunk000Sub000Block162Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part004] using hcert

def TailChunk000Sub000Block162Part005SupportExplicit : Finset ℕ :=
  ([6719] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part005 : ℚ :=
  (705390015625 : ℚ) / 1273288643408930322

def SurrogateDiagonalTailChunk000Sub000Block162Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6719
    = surrogateDiagTailX0RatChunk000Sub000Block162Part005

theorem surrogateDiagonalTailChunk000Sub000Block162Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part005] using hcert

def TailChunk000Sub000Block162Part006SupportExplicit : Finset ℕ :=
  ([6721] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part006 : ℚ :=
  (5846156977 : ℚ) / 6190873101434880

def SurrogateDiagonalTailChunk000Sub000Block162Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6721
    = surrogateDiagTailX0RatChunk000Sub000Block162Part006

theorem surrogateDiagonalTailChunk000Sub000Block162Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part006] using hcert

def TailChunk000Sub000Block162Part007SupportExplicit : Finset ℕ :=
  ([6722] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part007 : ℚ :=
  (56470308679 : ℚ) / 12748055917363200

def SurrogateDiagonalTailChunk000Sub000Block162Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6722
    = surrogateDiagTailX0RatChunk000Sub000Block162Part007

theorem surrogateDiagonalTailChunk000Sub000Block162Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part007] using hcert

def TailChunk000Sub000Block162Part008SupportExplicit : Finset ℕ :=
  ([6726] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part008 : ℚ :=
  (363205844525 : ℚ) / 23763961523856384

def SurrogateDiagonalTailChunk000Sub000Block162Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6726
    = surrogateDiagTailX0RatChunk000Sub000Block162Part008

theorem surrogateDiagonalTailChunk000Sub000Block162Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part008] using hcert

def TailChunk000Sub000Block162Part009SupportExplicit : Finset ℕ :=
  ([6729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part009 : ℚ :=
  (188558625 : ℚ) / 101065382584384

def SurrogateDiagonalTailChunk000Sub000Block162Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6729
    = surrogateDiagTailX0RatChunk000Sub000Block162Part009

theorem surrogateDiagonalTailChunk000Sub000Block162Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part009] using hcert

def TailChunk000Sub000Block162Part010SupportExplicit : Finset ℕ :=
  ([6730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part010 : ℚ :=
  (1073952865075 : ℚ) / 130540092593799168

def SurrogateDiagonalTailChunk000Sub000Block162Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6730
    = surrogateDiagTailX0RatChunk000Sub000Block162Part010

theorem surrogateDiagonalTailChunk000Sub000Block162Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part010] using hcert

def TailChunk000Sub000Block162Part011SupportExplicit : Finset ℕ :=
  ([6731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part011 : ℚ :=
  (1368724559375 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub000Block162Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6731
    = surrogateDiagTailX0RatChunk000Sub000Block162Part011

theorem surrogateDiagonalTailChunk000Sub000Block162Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part011] using hcert

def TailChunk000Sub000Block162Part012SupportExplicit : Finset ℕ :=
  ([6733] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part012 : ℚ :=
  (708332640625 : ℚ) / 1283935765425283872

def SurrogateDiagonalTailChunk000Sub000Block162Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6733
    = surrogateDiagTailX0RatChunk000Sub000Block162Part012

theorem surrogateDiagonalTailChunk000Sub000Block162Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part012] using hcert

def TailChunk000Sub000Block162Part013SupportExplicit : Finset ℕ :=
  ([6734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part013 : ℚ :=
  (608200965775 : ℚ) / 112866965177499648

def SurrogateDiagonalTailChunk000Sub000Block162Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6734
    = surrogateDiagTailX0RatChunk000Sub000Block162Part013

theorem surrogateDiagonalTailChunk000Sub000Block162Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part013] using hcert

def TailChunk000Sub000Block162Part014SupportExplicit : Finset ℕ :=
  ([6735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part014 : ℚ :=
  (104943759225 : ℚ) / 68761859473276928

def SurrogateDiagonalTailChunk000Sub000Block162Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6735
    = surrogateDiagTailX0RatChunk000Sub000Block162Part014

theorem surrogateDiagonalTailChunk000Sub000Block162Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part014] using hcert

def TailChunk000Sub000Block162Part015SupportExplicit : Finset ℕ :=
  ([6737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part015 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block162Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6737
    = surrogateDiagTailX0RatChunk000Sub000Block162Part015

theorem surrogateDiagonalTailChunk000Sub000Block162Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part015] using hcert

def TailChunk000Sub000Block162Part016SupportExplicit : Finset ℕ :=
  ([6738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part016 : ℚ :=
  (551480950675 : ℚ) / 63404235329643648

def SurrogateDiagonalTailChunk000Sub000Block162Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6738
    = surrogateDiagTailX0RatChunk000Sub000Block162Part016

theorem surrogateDiagonalTailChunk000Sub000Block162Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part016] using hcert

def TailChunk000Sub000Block162Part017SupportExplicit : Finset ℕ :=
  ([6739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part017 : ℚ :=
  (32388597675 : ℚ) / 1419474951544477696

def SurrogateDiagonalTailChunk000Sub000Block162Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6739
    = surrogateDiagTailX0RatChunk000Sub000Block162Part017

theorem surrogateDiagonalTailChunk000Sub000Block162Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part017] using hcert

def TailChunk000Sub000Block162Part018SupportExplicit : Finset ℕ :=
  ([6742] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part018 : ℚ :=
  (284091025 : ℚ) / 129004973445522

def SurrogateDiagonalTailChunk000Sub000Block162Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6742
    = surrogateDiagTailX0RatChunk000Sub000Block162Part018

theorem surrogateDiagonalTailChunk000Sub000Block162Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part018] using hcert

def TailChunk000Sub000Block162Part019SupportExplicit : Finset ℕ :=
  ([6743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part019 : ℚ :=
  (2535151321 : ℚ) / 46770421525862400

def SurrogateDiagonalTailChunk000Sub000Block162Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6743
    = surrogateDiagTailX0RatChunk000Sub000Block162Part019

theorem surrogateDiagonalTailChunk000Sub000Block162Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part019] using hcert

def TailChunk000Sub000Block162Part020SupportExplicit : Finset ℕ :=
  ([6745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part020 : ℚ :=
  (10067565227 : ℚ) / 32268516540825600

def SurrogateDiagonalTailChunk000Sub000Block162Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6745
    = surrogateDiagTailX0RatChunk000Sub000Block162Part020

theorem surrogateDiagonalTailChunk000Sub000Block162Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part020] using hcert

def TailChunk000Sub000Block162Part021SupportExplicit : Finset ℕ :=
  ([6746] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part021 : ℚ :=
  (177767640625 : ℚ) / 80819680896198432

def SurrogateDiagonalTailChunk000Sub000Block162Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6746
    = surrogateDiagTailX0RatChunk000Sub000Block162Part021

theorem surrogateDiagonalTailChunk000Sub000Block162Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part021] using hcert

def TailChunk000Sub000Block162Part022SupportExplicit : Finset ℕ :=
  ([6747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part022 : ℚ :=
  (322619682125 : ℚ) / 363040952256036864

def SurrogateDiagonalTailChunk000Sub000Block162Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6747
    = surrogateDiagTailX0RatChunk000Sub000Block162Part022

theorem surrogateDiagonalTailChunk000Sub000Block162Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part022] using hcert

def TailChunk000Sub000Block162Part023SupportExplicit : Finset ℕ :=
  ([6749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part023 : ℚ :=
  (132104295025 : ℚ) / 4029837493464465408

def SurrogateDiagonalTailChunk000Sub000Block162Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6749
    = surrogateDiagTailX0RatChunk000Sub000Block162Part023

theorem surrogateDiagonalTailChunk000Sub000Block162Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part023] using hcert

def TailChunk000Sub000Block162Part024SupportExplicit : Finset ℕ :=
  ([6751] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block162Part024 : ℚ :=
  (30783794225 : ℚ) / 2304052752306299904

def SurrogateDiagonalTailChunk000Sub000Block162Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 6751
    = surrogateDiagTailX0RatChunk000Sub000Block162Part024

theorem surrogateDiagonalTailChunk000Sub000Block162Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block162Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block162Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block162Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block162Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block162Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block162HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block162Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block162Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part000
    + surrogateDiagTailX0RatChunk000Sub000Block162Part001
    + surrogateDiagTailX0RatChunk000Sub000Block162Part002
    + surrogateDiagTailX0RatChunk000Sub000Block162Part003
    + surrogateDiagTailX0RatChunk000Sub000Block162Part004
    + surrogateDiagTailX0RatChunk000Sub000Block162Part005
    + surrogateDiagTailX0RatChunk000Sub000Block162Part006
    + surrogateDiagTailX0RatChunk000Sub000Block162Part007
    + surrogateDiagTailX0RatChunk000Sub000Block162Part008
    + surrogateDiagTailX0RatChunk000Sub000Block162Part009

def surrogateDiagonalTailChunk000Sub000Block162MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block162Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block162Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part010
    + surrogateDiagTailX0RatChunk000Sub000Block162Part011
    + surrogateDiagTailX0RatChunk000Sub000Block162Part012
    + surrogateDiagTailX0RatChunk000Sub000Block162Part013
    + surrogateDiagTailX0RatChunk000Sub000Block162Part014
    + surrogateDiagTailX0RatChunk000Sub000Block162Part015
    + surrogateDiagTailX0RatChunk000Sub000Block162Part016
    + surrogateDiagTailX0RatChunk000Sub000Block162Part017
    + surrogateDiagTailX0RatChunk000Sub000Block162Part018
    + surrogateDiagTailX0RatChunk000Sub000Block162Part019

def surrogateDiagonalTailChunk000Sub000Block162TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block162Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block162Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block162Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part020
    + surrogateDiagTailX0RatChunk000Sub000Block162Part021
    + surrogateDiagTailX0RatChunk000Sub000Block162Part022
    + surrogateDiagTailX0RatChunk000Sub000Block162Part023
    + surrogateDiagTailX0RatChunk000Sub000Block162Part024

def surrogateDiagonalTailChunk000Sub000Block162Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block162HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block162MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block162TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block162 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block162Part000
    + surrogateDiagTailX0RatChunk000Sub000Block162Part001
    + surrogateDiagTailX0RatChunk000Sub000Block162Part002
    + surrogateDiagTailX0RatChunk000Sub000Block162Part003
    + surrogateDiagTailX0RatChunk000Sub000Block162Part004
    + surrogateDiagTailX0RatChunk000Sub000Block162Part005
    + surrogateDiagTailX0RatChunk000Sub000Block162Part006
    + surrogateDiagTailX0RatChunk000Sub000Block162Part007
    + surrogateDiagTailX0RatChunk000Sub000Block162Part008
    + surrogateDiagTailX0RatChunk000Sub000Block162Part009
    + surrogateDiagTailX0RatChunk000Sub000Block162Part010
    + surrogateDiagTailX0RatChunk000Sub000Block162Part011
    + surrogateDiagTailX0RatChunk000Sub000Block162Part012
    + surrogateDiagTailX0RatChunk000Sub000Block162Part013
    + surrogateDiagTailX0RatChunk000Sub000Block162Part014
    + surrogateDiagTailX0RatChunk000Sub000Block162Part015
    + surrogateDiagTailX0RatChunk000Sub000Block162Part016
    + surrogateDiagTailX0RatChunk000Sub000Block162Part017
    + surrogateDiagTailX0RatChunk000Sub000Block162Part018
    + surrogateDiagTailX0RatChunk000Sub000Block162Part019
    + surrogateDiagTailX0RatChunk000Sub000Block162Part020
    + surrogateDiagTailX0RatChunk000Sub000Block162Part021
    + surrogateDiagTailX0RatChunk000Sub000Block162Part022
    + surrogateDiagTailX0RatChunk000Sub000Block162Part023
    + surrogateDiagTailX0RatChunk000Sub000Block162Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block162_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block162Head + surrogateDiagTailX0RatChunk000Sub000Block162Mid + surrogateDiagTailX0RatChunk000Sub000Block162Tail =
      surrogateDiagTailX0RatChunk000Sub000Block162 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block162Head surrogateDiagTailX0RatChunk000Sub000Block162Mid surrogateDiagTailX0RatChunk000Sub000Block162Tail surrogateDiagTailX0RatChunk000Sub000Block162
  ring

def SurrogateDiagonalTailChunk000Sub000Block162HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block162HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block162Head

def SurrogateDiagonalTailChunk000Sub000Block162MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block162MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block162Mid

def SurrogateDiagonalTailChunk000Sub000Block162TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block162TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block162Tail

theorem surrogateDiagonalTailChunk000Sub000Block162_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block162HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block162MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block162TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block162Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block162 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block162HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block162MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block162TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block162Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block162_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
