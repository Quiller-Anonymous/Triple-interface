import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [138,139). -/

/- Block 138 covers tail-support indices [3450,3475) and q from 5729 to 5770. -/

def TailChunk000Sub000Block138Part000SupportExplicit : Finset ℕ :=
  ([5729] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part000 : ℚ :=
  (2784952775 : ℚ) / 3044666882654208

def SurrogateDiagonalTailChunk000Sub000Block138Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5729
    = surrogateDiagTailX0RatChunk000Sub000Block138Part000

theorem surrogateDiagonalTailChunk000Sub000Block138Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part000] using hcert

def TailChunk000Sub000Block138Part001SupportExplicit : Finset ℕ :=
  ([5730] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part001 : ℚ :=
  (3296269209 : ℚ) / 88983595827200

def SurrogateDiagonalTailChunk000Sub000Block138Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5730
    = surrogateDiagTailX0RatChunk000Sub000Block138Part001

theorem surrogateDiagonalTailChunk000Sub000Block138Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part001] using hcert

def TailChunk000Sub000Block138Part002SupportExplicit : Finset ℕ :=
  ([5731] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part002 : ℚ :=
  (2306983457 : ℚ) / 2285336976000000

def SurrogateDiagonalTailChunk000Sub000Block138Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5731
    = surrogateDiagTailX0RatChunk000Sub000Block138Part002

theorem surrogateDiagonalTailChunk000Sub000Block138Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part002] using hcert

def TailChunk000Sub000Block138Part003SupportExplicit : Finset ℕ :=
  ([5734] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part003 : ℚ :=
  (39377789539 : ℚ) / 5803943532595200

def SurrogateDiagonalTailChunk000Sub000Block138Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5734
    = surrogateDiagTailX0RatChunk000Sub000Block138Part003

theorem surrogateDiagonalTailChunk000Sub000Block138Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part003] using hcert

def TailChunk000Sub000Block138Part004SupportExplicit : Finset ℕ :=
  ([5735] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part004 : ℚ :=
  (341639941 : ℚ) / 193530461552640

def SurrogateDiagonalTailChunk000Sub000Block138Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5735
    = surrogateDiagTailX0RatChunk000Sub000Block138Part004

theorem surrogateDiagonalTailChunk000Sub000Block138Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part004] using hcert

def TailChunk000Sub000Block138Part005SupportExplicit : Finset ℕ :=
  ([5737] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part005 : ℚ :=
  (514268265625 : ℚ) / 676711314997719552

def SurrogateDiagonalTailChunk000Sub000Block138Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5737
    = surrogateDiagTailX0RatChunk000Sub000Block138Part005

theorem surrogateDiagonalTailChunk000Sub000Block138Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part005] using hcert

def TailChunk000Sub000Block138Part006SupportExplicit : Finset ℕ :=
  ([5738] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part006 : ℚ :=
  (853873841 : ℚ) / 118121619600000

def SurrogateDiagonalTailChunk000Sub000Block138Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5738
    = surrogateDiagTailX0RatChunk000Sub000Block138Part006

theorem surrogateDiagonalTailChunk000Sub000Block138Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part006] using hcert

def TailChunk000Sub000Block138Part007SupportExplicit : Finset ℕ :=
  ([5739] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part007 : ℚ :=
  (228750770075 : ℚ) / 267342741727494144

def SurrogateDiagonalTailChunk000Sub000Block138Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5739
    = surrogateDiagTailX0RatChunk000Sub000Block138Part007

theorem surrogateDiagonalTailChunk000Sub000Block138Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part007] using hcert

def TailChunk000Sub000Block138Part008SupportExplicit : Finset ℕ :=
  ([5741] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part008 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block138Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5741
    = surrogateDiagTailX0RatChunk000Sub000Block138Part008

theorem surrogateDiagonalTailChunk000Sub000Block138Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part008] using hcert

def TailChunk000Sub000Block138Part009SupportExplicit : Finset ℕ :=
  ([5743] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part009 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block138Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5743
    = surrogateDiagTailX0RatChunk000Sub000Block138Part009

theorem surrogateDiagonalTailChunk000Sub000Block138Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part009] using hcert

def TailChunk000Sub000Block138Part010SupportExplicit : Finset ℕ :=
  ([5745] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part010 : ℚ :=
  (504063597475 : ℚ) / 218092262796853248

def SurrogateDiagonalTailChunk000Sub000Block138Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5745
    = surrogateDiagTailX0RatChunk000Sub000Block138Part010

theorem surrogateDiagonalTailChunk000Sub000Block138Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part010] using hcert

def TailChunk000Sub000Block138Part011SupportExplicit : Finset ℕ :=
  ([5747] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part011 : ℚ :=
  (140984399 : ℚ) / 813981931833600

def SurrogateDiagonalTailChunk000Sub000Block138Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5747
    = surrogateDiagTailX0RatChunk000Sub000Block138Part011

theorem surrogateDiagonalTailChunk000Sub000Block138Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part011] using hcert

def TailChunk000Sub000Block138Part012SupportExplicit : Finset ℕ :=
  ([5749] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part012 : ℚ :=
  (516421890625 : ℚ) / 682391966456830752

def SurrogateDiagonalTailChunk000Sub000Block138Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5749
    = surrogateDiagTailX0RatChunk000Sub000Block138Part012

theorem surrogateDiagonalTailChunk000Sub000Block138Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part012] using hcert

def TailChunk000Sub000Block138Part013SupportExplicit : Finset ℕ :=
  ([5753] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part013 : ℚ :=
  (73709721223 : ℚ) / 74262379762051200

def SurrogateDiagonalTailChunk000Sub000Block138Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5753
    = surrogateDiagTailX0RatChunk000Sub000Block138Part013

theorem surrogateDiagonalTailChunk000Sub000Block138Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part013] using hcert

def TailChunk000Sub000Block138Part014SupportExplicit : Finset ℕ :=
  ([5754] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part014 : ℚ :=
  (266629934225 : ℚ) / 8869057711570944

def SurrogateDiagonalTailChunk000Sub000Block138Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5754
    = surrogateDiagTailX0RatChunk000Sub000Block138Part014

theorem surrogateDiagonalTailChunk000Sub000Block138Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part014] using hcert

def TailChunk000Sub000Block138Part015SupportExplicit : Finset ℕ :=
  ([5755] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part015 : ℚ :=
  (15720164611 : ℚ) / 11195878728000000

def SurrogateDiagonalTailChunk000Sub000Block138Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5755
    = surrogateDiagTailX0RatChunk000Sub000Block138Part015

theorem surrogateDiagonalTailChunk000Sub000Block138Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part015] using hcert

def TailChunk000Sub000Block138Part016SupportExplicit : Finset ℕ :=
  ([5757] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part016 : ℚ :=
  (17118573283 : ℚ) / 5599839744000000

def SurrogateDiagonalTailChunk000Sub000Block138Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5757
    = surrogateDiagTailX0RatChunk000Sub000Block138Part016

theorem surrogateDiagonalTailChunk000Sub000Block138Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part016] using hcert

def TailChunk000Sub000Block138Part017SupportExplicit : Finset ℕ :=
  ([5758] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part017 : ℚ :=
  (1035872908975 : ℚ) / 171549721477318728

def SurrogateDiagonalTailChunk000Sub000Block138Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5758
    = surrogateDiagTailX0RatChunk000Sub000Block138Part017

theorem surrogateDiagonalTailChunk000Sub000Block138Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part017] using hcert

def TailChunk000Sub000Block138Part018SupportExplicit : Finset ℕ :=
  ([5759] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part018 : ℚ :=
  (628163158475 : ℚ) / 659659263802546176

def SurrogateDiagonalTailChunk000Sub000Block138Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5759
    = surrogateDiagTailX0RatChunk000Sub000Block138Part018

theorem surrogateDiagonalTailChunk000Sub000Block138Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part018] using hcert

def TailChunk000Sub000Block138Part019SupportExplicit : Finset ℕ :=
  ([5761] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part019 : ℚ :=
  (1733650258975 : ℚ) / 1479514175519810688

def SurrogateDiagonalTailChunk000Sub000Block138Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5761
    = surrogateDiagTailX0RatChunk000Sub000Block138Part019

theorem surrogateDiagonalTailChunk000Sub000Block138Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part019] using hcert

def TailChunk000Sub000Block138Part020SupportExplicit : Finset ℕ :=
  ([5762] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part020 : ℚ :=
  (993544109725 : ℚ) / 147638547085696128

def SurrogateDiagonalTailChunk000Sub000Block138Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5762
    = surrogateDiagTailX0RatChunk000Sub000Block138Part020

theorem surrogateDiagonalTailChunk000Sub000Block138Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part020] using hcert

def TailChunk000Sub000Block138Part021SupportExplicit : Finset ℕ :=
  ([5763] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part021 : ℚ :=
  (270060237175 : ℚ) / 103142789209915392

def SurrogateDiagonalTailChunk000Sub000Block138Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5763
    = surrogateDiagTailX0RatChunk000Sub000Block138Part021

theorem surrogateDiagonalTailChunk000Sub000Block138Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part021] using hcert

def TailChunk000Sub000Block138Part022SupportExplicit : Finset ℕ :=
  ([5765] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part022 : ℚ :=
  (262914124525 : ℚ) / 187899441900945408

def SurrogateDiagonalTailChunk000Sub000Block138Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5765
    = surrogateDiagTailX0RatChunk000Sub000Block138Part022

theorem surrogateDiagonalTailChunk000Sub000Block138Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part022] using hcert

def TailChunk000Sub000Block138Part023SupportExplicit : Finset ℕ :=
  ([5767] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part023 : ℚ :=
  (2017198749175 : ℚ) / 2487340580582227968

def SurrogateDiagonalTailChunk000Sub000Block138Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5767
    = surrogateDiagTailX0RatChunk000Sub000Block138Part023

theorem surrogateDiagonalTailChunk000Sub000Block138Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part023] using hcert

def TailChunk000Sub000Block138Part024SupportExplicit : Finset ℕ :=
  ([5770] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block138Part024 : ℚ :=
  (7501022675 : ℚ) / 652428617711616

def SurrogateDiagonalTailChunk000Sub000Block138Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 5770
    = surrogateDiagTailX0RatChunk000Sub000Block138Part024

theorem surrogateDiagonalTailChunk000Sub000Block138Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block138Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block138Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block138Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block138Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block138Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block138Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block138HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block138Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block138Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block138Part000
    + surrogateDiagTailX0RatChunk000Sub000Block138Part001
    + surrogateDiagTailX0RatChunk000Sub000Block138Part002
    + surrogateDiagTailX0RatChunk000Sub000Block138Part003
    + surrogateDiagTailX0RatChunk000Sub000Block138Part004
    + surrogateDiagTailX0RatChunk000Sub000Block138Part005
    + surrogateDiagTailX0RatChunk000Sub000Block138Part006
    + surrogateDiagTailX0RatChunk000Sub000Block138Part007
    + surrogateDiagTailX0RatChunk000Sub000Block138Part008
    + surrogateDiagTailX0RatChunk000Sub000Block138Part009

def surrogateDiagonalTailChunk000Sub000Block138MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block138Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block138Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block138Part010
    + surrogateDiagTailX0RatChunk000Sub000Block138Part011
    + surrogateDiagTailX0RatChunk000Sub000Block138Part012
    + surrogateDiagTailX0RatChunk000Sub000Block138Part013
    + surrogateDiagTailX0RatChunk000Sub000Block138Part014
    + surrogateDiagTailX0RatChunk000Sub000Block138Part015
    + surrogateDiagTailX0RatChunk000Sub000Block138Part016
    + surrogateDiagTailX0RatChunk000Sub000Block138Part017
    + surrogateDiagTailX0RatChunk000Sub000Block138Part018
    + surrogateDiagTailX0RatChunk000Sub000Block138Part019

def surrogateDiagonalTailChunk000Sub000Block138TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block138Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block138Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block138Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block138Part020
    + surrogateDiagTailX0RatChunk000Sub000Block138Part021
    + surrogateDiagTailX0RatChunk000Sub000Block138Part022
    + surrogateDiagTailX0RatChunk000Sub000Block138Part023
    + surrogateDiagTailX0RatChunk000Sub000Block138Part024

def surrogateDiagonalTailChunk000Sub000Block138Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block138HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block138MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block138TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block138 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block138Part000
    + surrogateDiagTailX0RatChunk000Sub000Block138Part001
    + surrogateDiagTailX0RatChunk000Sub000Block138Part002
    + surrogateDiagTailX0RatChunk000Sub000Block138Part003
    + surrogateDiagTailX0RatChunk000Sub000Block138Part004
    + surrogateDiagTailX0RatChunk000Sub000Block138Part005
    + surrogateDiagTailX0RatChunk000Sub000Block138Part006
    + surrogateDiagTailX0RatChunk000Sub000Block138Part007
    + surrogateDiagTailX0RatChunk000Sub000Block138Part008
    + surrogateDiagTailX0RatChunk000Sub000Block138Part009
    + surrogateDiagTailX0RatChunk000Sub000Block138Part010
    + surrogateDiagTailX0RatChunk000Sub000Block138Part011
    + surrogateDiagTailX0RatChunk000Sub000Block138Part012
    + surrogateDiagTailX0RatChunk000Sub000Block138Part013
    + surrogateDiagTailX0RatChunk000Sub000Block138Part014
    + surrogateDiagTailX0RatChunk000Sub000Block138Part015
    + surrogateDiagTailX0RatChunk000Sub000Block138Part016
    + surrogateDiagTailX0RatChunk000Sub000Block138Part017
    + surrogateDiagTailX0RatChunk000Sub000Block138Part018
    + surrogateDiagTailX0RatChunk000Sub000Block138Part019
    + surrogateDiagTailX0RatChunk000Sub000Block138Part020
    + surrogateDiagTailX0RatChunk000Sub000Block138Part021
    + surrogateDiagTailX0RatChunk000Sub000Block138Part022
    + surrogateDiagTailX0RatChunk000Sub000Block138Part023
    + surrogateDiagTailX0RatChunk000Sub000Block138Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block138_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block138Head + surrogateDiagTailX0RatChunk000Sub000Block138Mid + surrogateDiagTailX0RatChunk000Sub000Block138Tail =
      surrogateDiagTailX0RatChunk000Sub000Block138 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block138Head surrogateDiagTailX0RatChunk000Sub000Block138Mid surrogateDiagTailX0RatChunk000Sub000Block138Tail surrogateDiagTailX0RatChunk000Sub000Block138
  ring

def SurrogateDiagonalTailChunk000Sub000Block138HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block138HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block138Head

def SurrogateDiagonalTailChunk000Sub000Block138MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block138MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block138Mid

def SurrogateDiagonalTailChunk000Sub000Block138TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block138TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block138Tail

theorem surrogateDiagonalTailChunk000Sub000Block138_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block138HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block138MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block138TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block138Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block138 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block138HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block138MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block138TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block138Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block138_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
