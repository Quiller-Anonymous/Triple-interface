import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [196,197). -/

/-- Block 196 covers tail-support indices [4900,4925) and q from 8106 to 8147. -/

def TailChunk000Sub000Block196Part000SupportExplicit : Finset ℕ :=
  ([8106] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part000 : ℚ :=
  (609805908775 : ℚ) / 70462290712854528

def SurrogateDiagonalTailChunk000Sub000Block196Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8106
    = surrogateDiagTailX0RatChunk000Sub000Block196Part000

theorem surrogateDiagonalTailChunk000Sub000Block196Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part000] using hcert

def TailChunk000Sub000Block196Part001SupportExplicit : Finset ℕ :=
  ([8110] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part001 : ℚ :=
  (6900360887 : ℚ) / 2204432913623040

def SurrogateDiagonalTailChunk000Sub000Block196Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8110
    = surrogateDiagTailX0RatChunk000Sub000Block196Part001

theorem surrogateDiagonalTailChunk000Sub000Block196Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part001] using hcert

def TailChunk000Sub000Block196Part002SupportExplicit : Finset ℕ :=
  ([8111] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part002 : ℚ :=
  (1644708025 : ℚ) / 4326834332237682

def SurrogateDiagonalTailChunk000Sub000Block196Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8111
    = surrogateDiagTailX0RatChunk000Sub000Block196Part002

theorem surrogateDiagonalTailChunk000Sub000Block196Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part002] using hcert

def TailChunk000Sub000Block196Part003SupportExplicit : Finset ℕ :=
  ([8113] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part003 : ℚ :=
  (119209277671 : ℚ) / 176354633089843200

def SurrogateDiagonalTailChunk000Sub000Block196Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8113
    = surrogateDiagTailX0RatChunk000Sub000Block196Part003

theorem surrogateDiagonalTailChunk000Sub000Block196Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part003] using hcert

def TailChunk000Sub000Block196Part004SupportExplicit : Finset ℕ :=
  ([8114] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part004 : ℚ :=
  (257175765625 : ℚ) / 169183752291021312

def SurrogateDiagonalTailChunk000Sub000Block196Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8114
    = surrogateDiagTailX0RatChunk000Sub000Block196Part004

theorem surrogateDiagonalTailChunk000Sub000Block196Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part004] using hcert

def TailChunk000Sub000Block196Part005SupportExplicit : Finset ℕ :=
  ([8115] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part005 : ℚ :=
  (3772592569 : ℚ) / 1935304615526400

def SurrogateDiagonalTailChunk000Sub000Block196Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8115
    = surrogateDiagTailX0RatChunk000Sub000Block196Part005

theorem surrogateDiagonalTailChunk000Sub000Block196Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part005] using hcert

def TailChunk000Sub000Block196Part006SupportExplicit : Finset ℕ :=
  ([8117] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part006 : ℚ :=
  (1029463890625 : ℚ) / 2712283119239176992

def SurrogateDiagonalTailChunk000Sub000Block196Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8117
    = surrogateDiagTailX0RatChunk000Sub000Block196Part006

theorem surrogateDiagonalTailChunk000Sub000Block196Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part006] using hcert

def TailChunk000Sub000Block196Part007SupportExplicit : Finset ℕ :=
  ([8119] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part007 : ℚ :=
  (3856244345425 : ℚ) / 8992661292762267648

def SurrogateDiagonalTailChunk000Sub000Block196Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8119
    = surrogateDiagTailX0RatChunk000Sub000Block196Part007

theorem surrogateDiagonalTailChunk000Sub000Block196Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part007] using hcert

def TailChunk000Sub000Block196Part008SupportExplicit : Finset ℕ :=
  ([8121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part008 : ℚ :=
  (35769566275 : ℚ) / 33517995367431762

def SurrogateDiagonalTailChunk000Sub000Block196Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8121
    = surrogateDiagTailX0RatChunk000Sub000Block196Part008

theorem surrogateDiagonalTailChunk000Sub000Block196Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part008] using hcert

def TailChunk000Sub000Block196Part009SupportExplicit : Finset ℕ :=
  ([8122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part009 : ℚ :=
  (39967838227 : ℚ) / 23139036882000000

def SurrogateDiagonalTailChunk000Sub000Block196Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8122
    = surrogateDiagTailX0RatChunk000Sub000Block196Part009

theorem surrogateDiagonalTailChunk000Sub000Block196Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part009] using hcert

def TailChunk000Sub000Block196Part010SupportExplicit : Finset ℕ :=
  ([8123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part010 : ℚ :=
  (1030986390625 : ℚ) / 2720312569141493682

def SurrogateDiagonalTailChunk000Sub000Block196Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8123
    = surrogateDiagTailX0RatChunk000Sub000Block196Part010

theorem surrogateDiagonalTailChunk000Sub000Block196Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part010] using hcert

def TailChunk000Sub000Block196Part011SupportExplicit : Finset ℕ :=
  ([8126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part011 : ℚ :=
  (4797740625 : ℚ) / 2577415585267712

def SurrogateDiagonalTailChunk000Sub000Block196Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8126
    = surrogateDiagTailX0RatChunk000Sub000Block196Part011

theorem surrogateDiagonalTailChunk000Sub000Block196Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part011] using hcert

def TailChunk000Sub000Block196Part012SupportExplicit : Finset ℕ :=
  ([8129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part012 : ℚ :=
  (963200293 : ℚ) / 1977976094355648

def SurrogateDiagonalTailChunk000Sub000Block196Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8129
    = surrogateDiagTailX0RatChunk000Sub000Block196Part012

theorem surrogateDiagonalTailChunk000Sub000Block196Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part012] using hcert

def TailChunk000Sub000Block196Part013SupportExplicit : Finset ℕ :=
  ([8130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part013 : ℚ :=
  (5766950647 : ℚ) / 544304423116800

def SurrogateDiagonalTailChunk000Sub000Block196Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8130
    = surrogateDiagTailX0RatChunk000Sub000Block196Part013

theorem surrogateDiagonalTailChunk000Sub000Block196Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part013] using hcert

def TailChunk000Sub000Block196Part014SupportExplicit : Finset ℕ :=
  ([8131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part014 : ℚ :=
  (3979119430675 : ℚ) / 9798779236138272768

def SurrogateDiagonalTailChunk000Sub000Block196Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8131
    = surrogateDiagTailX0RatChunk000Sub000Block196Part014

theorem surrogateDiagonalTailChunk000Sub000Block196Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part014] using hcert

def TailChunk000Sub000Block196Part015SupportExplicit : Finset ℕ :=
  ([8133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part015 : ℚ :=
  (22960233247 : ℚ) / 21578636788384800

def SurrogateDiagonalTailChunk000Sub000Block196Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8133
    = surrogateDiagTailX0RatChunk000Sub000Block196Part015

theorem surrogateDiagonalTailChunk000Sub000Block196Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part015] using hcert

def TailChunk000Sub000Block196Part016SupportExplicit : Finset ℕ :=
  ([8135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part016 : ℚ :=
  (2976073465825 : ℚ) / 4474546124439472128

def SurrogateDiagonalTailChunk000Sub000Block196Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8135
    = surrogateDiagTailX0RatChunk000Sub000Block196Part016

theorem surrogateDiagonalTailChunk000Sub000Block196Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part016] using hcert

def TailChunk000Sub000Block196Part017SupportExplicit : Finset ℕ :=
  ([8137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part017 : ℚ :=
  (4011236686675 : ℚ) / 10018575069001170048

def SurrogateDiagonalTailChunk000Sub000Block196Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8137
    = surrogateDiagTailX0RatChunk000Sub000Block196Part017

theorem surrogateDiagonalTailChunk000Sub000Block196Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part017] using hcert

def TailChunk000Sub000Block196Part018SupportExplicit : Finset ℕ :=
  ([8138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part018 : ℚ :=
  (204594299675 : ℚ) / 54591837159555072

def SurrogateDiagonalTailChunk000Sub000Block196Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8138
    = surrogateDiagTailX0RatChunk000Sub000Block196Part018

theorem surrogateDiagonalTailChunk000Sub000Block196Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part018] using hcert

def TailChunk000Sub000Block196Part019SupportExplicit : Finset ℕ :=
  ([8139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part019 : ℚ :=
  (1149706308425 : ℚ) / 1082120405667692544

def SurrogateDiagonalTailChunk000Sub000Block196Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8139
    = surrogateDiagTailX0RatChunk000Sub000Block196Part019

theorem surrogateDiagonalTailChunk000Sub000Block196Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part019] using hcert

def TailChunk000Sub000Block196Part020SupportExplicit : Finset ℕ :=
  ([8141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part020 : ℚ :=
  (3378089630875 : ℚ) / 5908216111837619328

def SurrogateDiagonalTailChunk000Sub000Block196Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8141
    = surrogateDiagTailX0RatChunk000Sub000Block196Part020

theorem surrogateDiagonalTailChunk000Sub000Block196Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part020] using hcert

def TailChunk000Sub000Block196Part021SupportExplicit : Finset ℕ :=
  ([8142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part021 : ℚ :=
  (32278226025 : ℚ) / 3213923973810176

def SurrogateDiagonalTailChunk000Sub000Block196Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8142
    = surrogateDiagTailX0RatChunk000Sub000Block196Part021

theorem surrogateDiagonalTailChunk000Sub000Block196Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part021] using hcert

def TailChunk000Sub000Block196Part022SupportExplicit : Finset ℕ :=
  ([8143] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part022 : ℚ :=
  (19813465125 : ℚ) / 44557123621249024

def SurrogateDiagonalTailChunk000Sub000Block196Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8143
    = surrogateDiagTailX0RatChunk000Sub000Block196Part022

theorem surrogateDiagonalTailChunk000Sub000Block196Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part022] using hcert

def TailChunk000Sub000Block196Part023SupportExplicit : Finset ℕ :=
  ([8146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part023 : ℚ :=
  (259208265625 : ℚ) / 171869156234015232

def SurrogateDiagonalTailChunk000Sub000Block196Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8146
    = surrogateDiagTailX0RatChunk000Sub000Block196Part023

theorem surrogateDiagonalTailChunk000Sub000Block196Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part023] using hcert

def TailChunk000Sub000Block196Part024SupportExplicit : Finset ℕ :=
  ([8147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block196Part024 : ℚ :=
  (0 : ℚ) / 1

def SurrogateDiagonalTailChunk000Sub000Block196Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 8147
    = surrogateDiagTailX0RatChunk000Sub000Block196Part024

theorem surrogateDiagonalTailChunk000Sub000Block196Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block196Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block196Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block196Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block196Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block196Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block196HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block196Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block196Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part000
    + surrogateDiagTailX0RatChunk000Sub000Block196Part001
    + surrogateDiagTailX0RatChunk000Sub000Block196Part002
    + surrogateDiagTailX0RatChunk000Sub000Block196Part003
    + surrogateDiagTailX0RatChunk000Sub000Block196Part004
    + surrogateDiagTailX0RatChunk000Sub000Block196Part005
    + surrogateDiagTailX0RatChunk000Sub000Block196Part006
    + surrogateDiagTailX0RatChunk000Sub000Block196Part007
    + surrogateDiagTailX0RatChunk000Sub000Block196Part008
    + surrogateDiagTailX0RatChunk000Sub000Block196Part009

def surrogateDiagonalTailChunk000Sub000Block196MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block196Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block196Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part010
    + surrogateDiagTailX0RatChunk000Sub000Block196Part011
    + surrogateDiagTailX0RatChunk000Sub000Block196Part012
    + surrogateDiagTailX0RatChunk000Sub000Block196Part013
    + surrogateDiagTailX0RatChunk000Sub000Block196Part014
    + surrogateDiagTailX0RatChunk000Sub000Block196Part015
    + surrogateDiagTailX0RatChunk000Sub000Block196Part016
    + surrogateDiagTailX0RatChunk000Sub000Block196Part017
    + surrogateDiagTailX0RatChunk000Sub000Block196Part018
    + surrogateDiagTailX0RatChunk000Sub000Block196Part019

def surrogateDiagonalTailChunk000Sub000Block196TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block196Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block196Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block196Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part020
    + surrogateDiagTailX0RatChunk000Sub000Block196Part021
    + surrogateDiagTailX0RatChunk000Sub000Block196Part022
    + surrogateDiagTailX0RatChunk000Sub000Block196Part023
    + surrogateDiagTailX0RatChunk000Sub000Block196Part024

def surrogateDiagonalTailChunk000Sub000Block196Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block196HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block196MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block196TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block196 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block196Part000
    + surrogateDiagTailX0RatChunk000Sub000Block196Part001
    + surrogateDiagTailX0RatChunk000Sub000Block196Part002
    + surrogateDiagTailX0RatChunk000Sub000Block196Part003
    + surrogateDiagTailX0RatChunk000Sub000Block196Part004
    + surrogateDiagTailX0RatChunk000Sub000Block196Part005
    + surrogateDiagTailX0RatChunk000Sub000Block196Part006
    + surrogateDiagTailX0RatChunk000Sub000Block196Part007
    + surrogateDiagTailX0RatChunk000Sub000Block196Part008
    + surrogateDiagTailX0RatChunk000Sub000Block196Part009
    + surrogateDiagTailX0RatChunk000Sub000Block196Part010
    + surrogateDiagTailX0RatChunk000Sub000Block196Part011
    + surrogateDiagTailX0RatChunk000Sub000Block196Part012
    + surrogateDiagTailX0RatChunk000Sub000Block196Part013
    + surrogateDiagTailX0RatChunk000Sub000Block196Part014
    + surrogateDiagTailX0RatChunk000Sub000Block196Part015
    + surrogateDiagTailX0RatChunk000Sub000Block196Part016
    + surrogateDiagTailX0RatChunk000Sub000Block196Part017
    + surrogateDiagTailX0RatChunk000Sub000Block196Part018
    + surrogateDiagTailX0RatChunk000Sub000Block196Part019
    + surrogateDiagTailX0RatChunk000Sub000Block196Part020
    + surrogateDiagTailX0RatChunk000Sub000Block196Part021
    + surrogateDiagTailX0RatChunk000Sub000Block196Part022
    + surrogateDiagTailX0RatChunk000Sub000Block196Part023
    + surrogateDiagTailX0RatChunk000Sub000Block196Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block196_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block196Head + surrogateDiagTailX0RatChunk000Sub000Block196Mid + surrogateDiagTailX0RatChunk000Sub000Block196Tail =
      surrogateDiagTailX0RatChunk000Sub000Block196 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block196Head surrogateDiagTailX0RatChunk000Sub000Block196Mid surrogateDiagTailX0RatChunk000Sub000Block196Tail surrogateDiagTailX0RatChunk000Sub000Block196
  ring

def SurrogateDiagonalTailChunk000Sub000Block196HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block196HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block196Head

def SurrogateDiagonalTailChunk000Sub000Block196MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block196MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block196Mid

def SurrogateDiagonalTailChunk000Sub000Block196TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block196TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block196Tail

theorem surrogateDiagonalTailChunk000Sub000Block196_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block196HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block196MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block196TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block196Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block196 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block196HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block196MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block196TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block196Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block196_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
