import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0TailPilot25

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated direct-term certificate blocks for tail chunk 000, subchunk 000, blocks [26,27). -/

/- Block 026 covers tail-support indices [650,675) and q from 1121 to 1159. -/

def TailChunk000Sub000Block026Part000SupportExplicit : Finset ℕ :=
  ([1121] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part000 : ℚ :=
  (73776400225 : ℚ) / 742623797620512

def SurrogateDiagonalTailChunk000Sub000Block026Part000CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1121
    = surrogateDiagTailX0RatChunk000Sub000Block026Part000

theorem surrogateDiagonalTailChunk000Sub000Block026Part000_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part000CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part000 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part000CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part000SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part000] using hcert

def TailChunk000Sub000Block026Part001SupportExplicit : Finset ℕ :=
  ([1122] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part001 : ℚ :=
  (25213807 : ℚ) / 6554910720

def SurrogateDiagonalTailChunk000Sub000Block026Part001CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1122
    = surrogateDiagTailX0RatChunk000Sub000Block026Part001

theorem surrogateDiagonalTailChunk000Sub000Block026Part001_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part001CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part001 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part001CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part001SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part001] using hcert

def TailChunk000Sub000Block026Part002SupportExplicit : Finset ℕ :=
  ([1123] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part002 : ℚ :=
  (157546540325 : ℚ) / 1981382354051364

def SurrogateDiagonalTailChunk000Sub000Block026Part002CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1123
    = surrogateDiagTailX0RatChunk000Sub000Block026Part002

theorem surrogateDiagonalTailChunk000Sub000Block026Part002_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part002CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part002 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part002CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part002SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part002] using hcert

def TailChunk000Sub000Block026Part003SupportExplicit : Finset ℕ :=
  ([1126] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part003 : ℚ :=
  (39565655425 : ℚ) / 62360864889042

def SurrogateDiagonalTailChunk000Sub000Block026Part003CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1126
    = surrogateDiagTailX0RatChunk000Sub000Block026Part003

theorem surrogateDiagonalTailChunk000Sub000Block026Part003_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part003CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part003 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part003CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part003SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part003] using hcert

def TailChunk000Sub000Block026Part004SupportExplicit : Finset ℕ :=
  ([1129] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part004 : ℚ :=
  (199003326125 : ℚ) / 2024106044580864

def SurrogateDiagonalTailChunk000Sub000Block026Part004CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1129
    = surrogateDiagTailX0RatChunk000Sub000Block026Part004

theorem surrogateDiagonalTailChunk000Sub000Block026Part004_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part004CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part004 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part004CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part004SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part004] using hcert

def TailChunk000Sub000Block026Part005SupportExplicit : Finset ℕ :=
  ([1130] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part005 : ℚ :=
  (71194110875 : ℚ) / 50362690043904

def SurrogateDiagonalTailChunk000Sub000Block026Part005CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1130
    = surrogateDiagTailX0RatChunk000Sub000Block026Part005

theorem surrogateDiagonalTailChunk000Sub000Block026Part005_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part005CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part005 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part005CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part005SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part005] using hcert

def TailChunk000Sub000Block026Part006SupportExplicit : Finset ℕ :=
  ([1131] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part006 : ℚ :=
  (28467661675 : ℚ) / 72846033813504

def SurrogateDiagonalTailChunk000Sub000Block026Part006CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1131
    = surrogateDiagTailX0RatChunk000Sub000Block026Part006

theorem surrogateDiagonalTailChunk000Sub000Block026Part006_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part006CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part006 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part006CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part006SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part006] using hcert

def TailChunk000Sub000Block026Part007SupportExplicit : Finset ℕ :=
  ([1133] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part007 : ℚ :=
  (11674692961 : ℚ) / 108264864643200

def SurrogateDiagonalTailChunk000Sub000Block026Part007CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1133
    = surrogateDiagTailX0RatChunk000Sub000Block026Part007

theorem surrogateDiagonalTailChunk000Sub000Block026Part007_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part007CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part007 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part007CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part007SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part007] using hcert

def TailChunk000Sub000Block026Part008SupportExplicit : Finset ℕ :=
  ([1135] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part008 : ℚ :=
  (263060355025 : ℚ) / 1669938897635328

def SurrogateDiagonalTailChunk000Sub000Block026Part008CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1135
    = surrogateDiagTailX0RatChunk000Sub000Block026Part008

theorem surrogateDiagonalTailChunk000Sub000Block026Part008_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part008CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part008 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part008CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part008SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part008] using hcert

def TailChunk000Sub000Block026Part009SupportExplicit : Finset ℕ :=
  ([1137] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part009 : ℚ :=
  (35816189575 : ℚ) / 116685260705664

def SurrogateDiagonalTailChunk000Sub000Block026Part009CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1137
    = surrogateDiagTailX0RatChunk000Sub000Block026Part009

theorem surrogateDiagonalTailChunk000Sub000Block026Part009_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part009CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part009 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part009CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part009SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part009] using hcert

def TailChunk000Sub000Block026Part010SupportExplicit : Finset ℕ :=
  ([1138] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part010 : ℚ :=
  (947000925 : ℚ) / 1355560711264

def SurrogateDiagonalTailChunk000Sub000Block026Part010CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1138
    = surrogateDiagTailX0RatChunk000Sub000Block026Part010

theorem surrogateDiagonalTailChunk000Sub000Block026Part010_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part010CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part010 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part010CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part010SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part010] using hcert

def TailChunk000Sub000Block026Part011SupportExplicit : Finset ℕ :=
  ([1139] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part011 : ℚ :=
  (186260070575 : ℚ) / 1554721255194624

def SurrogateDiagonalTailChunk000Sub000Block026Part011CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1139
    = surrogateDiagTailX0RatChunk000Sub000Block026Part011

theorem surrogateDiagonalTailChunk000Sub000Block026Part011_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part011CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part011 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part011CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part011SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part011] using hcert

def TailChunk000Sub000Block026Part012SupportExplicit : Finset ℕ :=
  ([1141] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part012 : ℚ :=
  (15688889825 : ℚ) / 123999351391296

def SurrogateDiagonalTailChunk000Sub000Block026Part012CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1141
    = surrogateDiagTailX0RatChunk000Sub000Block026Part012

theorem surrogateDiagonalTailChunk000Sub000Block026Part012_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part012CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part012 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part012CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part012SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part012] using hcert

def TailChunk000Sub000Block026Part013SupportExplicit : Finset ℕ :=
  ([1142] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part013 : ℚ :=
  (33908264 : ℚ) / 48880149075

def SurrogateDiagonalTailChunk000Sub000Block026Part013CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1142
    = surrogateDiagTailX0RatChunk000Sub000Block026Part013

theorem surrogateDiagonalTailChunk000Sub000Block026Part013_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part013CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part013 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part013CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part013SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part013] using hcert

def TailChunk000Sub000Block026Part014SupportExplicit : Finset ℕ :=
  ([1145] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part014 : ℚ :=
  (316455385975 : ℚ) / 1729841102880768

def SurrogateDiagonalTailChunk000Sub000Block026Part014CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1145
    = surrogateDiagTailX0RatChunk000Sub000Block026Part014

theorem surrogateDiagonalTailChunk000Sub000Block026Part014_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part014CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part014 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part014CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part014SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part014] using hcert

def TailChunk000Sub000Block026Part015SupportExplicit : Finset ℕ :=
  ([1146] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part015 : ℚ :=
  (1202266471 : ℚ) / 521388256800

def SurrogateDiagonalTailChunk000Sub000Block026Part015CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1146
    = surrogateDiagTailX0RatChunk000Sub000Block026Part015

theorem surrogateDiagonalTailChunk000Sub000Block026Part015_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part015CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part015 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part015CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part015SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part015] using hcert

def TailChunk000Sub000Block026Part016SupportExplicit : Finset ℕ :=
  ([1147] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part016 : ℚ :=
  (341483701 : ℚ) / 3023913461760

def SurrogateDiagonalTailChunk000Sub000Block026Part016CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1147
    = surrogateDiagTailX0RatChunk000Sub000Block026Part016

theorem surrogateDiagonalTailChunk000Sub000Block026Part016_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part016CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part016 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part016CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part016SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part016] using hcert

def TailChunk000Sub000Block026Part017SupportExplicit : Finset ℕ :=
  ([1149] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part017 : ℚ :=
  (114336852425 : ℚ) / 425961450775104

def SurrogateDiagonalTailChunk000Sub000Block026Part017CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1149
    = surrogateDiagTailX0RatChunk000Sub000Block026Part017

theorem surrogateDiagonalTailChunk000Sub000Block026Part017_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part017CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part017 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part017CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part017SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part017] using hcert

def TailChunk000Sub000Block026Part018SupportExplicit : Finset ℕ :=
  ([1151] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part018 : ℚ :=
  (6620030597 : ℚ) / 87467802562500

def SurrogateDiagonalTailChunk000Sub000Block026Part018CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1151
    = surrogateDiagTailX0RatChunk000Sub000Block026Part018

theorem surrogateDiagonalTailChunk000Sub000Block026Part018_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part018CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part018 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part018CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part018SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part018] using hcert

def TailChunk000Sub000Block026Part019SupportExplicit : Finset ℕ :=
  ([1153] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part019 : ℚ :=
  (166076419325 : ℚ) / 2201946584776704

def SurrogateDiagonalTailChunk000Sub000Block026Part019CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1153
    = surrogateDiagTailX0RatChunk000Sub000Block026Part019

theorem surrogateDiagonalTailChunk000Sub000Block026Part019_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part019CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part019 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part019CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part019SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part019] using hcert

def TailChunk000Sub000Block026Part020SupportExplicit : Finset ℕ :=
  ([1154] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part020 : ℚ :=
  (108201925 : ℚ) / 159284330496

def SurrogateDiagonalTailChunk000Sub000Block026Part020CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1154
    = surrogateDiagTailX0RatChunk000Sub000Block026Part020

theorem surrogateDiagonalTailChunk000Sub000Block026Part020_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part020CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part020 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part020CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part020SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part020] using hcert

def TailChunk000Sub000Block026Part021SupportExplicit : Finset ℕ :=
  ([1155] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part021 : ℚ :=
  (9293503 : ℚ) / 7865892864

def SurrogateDiagonalTailChunk000Sub000Block026Part021CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1155
    = surrogateDiagTailX0RatChunk000Sub000Block026Part021

theorem surrogateDiagonalTailChunk000Sub000Block026Part021_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part021CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part021 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part021CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part021SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part021] using hcert

def TailChunk000Sub000Block026Part022SupportExplicit : Finset ℕ :=
  ([1157] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part022 : ℚ :=
  (308209297525 : ℚ) / 3109442510389248

def SurrogateDiagonalTailChunk000Sub000Block026Part022CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1157
    = surrogateDiagTailX0RatChunk000Sub000Block026Part022

theorem surrogateDiagonalTailChunk000Sub000Block026Part022_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part022CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part022 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part022CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part022SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part022] using hcert

def TailChunk000Sub000Block026Part023SupportExplicit : Finset ℕ :=
  ([1158] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part023 : ℚ :=
  (61378946825 : ℚ) / 27184525737984

def SurrogateDiagonalTailChunk000Sub000Block026Part023CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1158
    = surrogateDiagTailX0RatChunk000Sub000Block026Part023

theorem surrogateDiagonalTailChunk000Sub000Block026Part023_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part023CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part023 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part023CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part023SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part023] using hcert

def TailChunk000Sub000Block026Part024SupportExplicit : Finset ℕ :=
  ([1159] : List ℕ).toFinset

def surrogateDiagTailX0RatChunk000Sub000Block026Part024 : ℚ :=
  (6294945983 : ℚ) / 68038052889600

def SurrogateDiagonalTailChunk000Sub000Block026Part024CertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 1159
    = surrogateDiagTailX0RatChunk000Sub000Block026Part024

theorem surrogateDiagonalTailChunk000Sub000Block026Part024_eq_cert_explicit :
    SurrogateDiagonalTailChunk000Sub000Block026Part024CertificateAtX0 →
    (∑ q ∈ TailChunk000Sub000Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
      = surrogateDiagTailX0RatChunk000Sub000Block026Part024 := by
  intro hcert
  unfold SurrogateDiagonalTailChunk000Sub000Block026Part024CertificateAtX0 at hcert
  simpa [TailChunk000Sub000Block026Part024SupportExplicit, surrogateDiagTailX0RatChunk000Sub000Block026Part024] using hcert

def surrogateDiagonalTailChunk000Sub000Block026HeadSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block026Part000SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part001SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part002SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part003SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part004SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part005SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part006SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part007SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part008SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part009SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block026Head : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block026Part000
    + surrogateDiagTailX0RatChunk000Sub000Block026Part001
    + surrogateDiagTailX0RatChunk000Sub000Block026Part002
    + surrogateDiagTailX0RatChunk000Sub000Block026Part003
    + surrogateDiagTailX0RatChunk000Sub000Block026Part004
    + surrogateDiagTailX0RatChunk000Sub000Block026Part005
    + surrogateDiagTailX0RatChunk000Sub000Block026Part006
    + surrogateDiagTailX0RatChunk000Sub000Block026Part007
    + surrogateDiagTailX0RatChunk000Sub000Block026Part008
    + surrogateDiagTailX0RatChunk000Sub000Block026Part009

def surrogateDiagonalTailChunk000Sub000Block026MidSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block026Part010SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part011SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part012SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part013SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part014SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part015SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part016SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part017SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part018SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part019SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block026Mid : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block026Part010
    + surrogateDiagTailX0RatChunk000Sub000Block026Part011
    + surrogateDiagTailX0RatChunk000Sub000Block026Part012
    + surrogateDiagTailX0RatChunk000Sub000Block026Part013
    + surrogateDiagTailX0RatChunk000Sub000Block026Part014
    + surrogateDiagTailX0RatChunk000Sub000Block026Part015
    + surrogateDiagTailX0RatChunk000Sub000Block026Part016
    + surrogateDiagTailX0RatChunk000Sub000Block026Part017
    + surrogateDiagTailX0RatChunk000Sub000Block026Part018
    + surrogateDiagTailX0RatChunk000Sub000Block026Part019

def surrogateDiagonalTailChunk000Sub000Block026TailSum (X0 : ℕ) : ℚ :=
  (∑ q ∈ TailChunk000Sub000Block026Part020SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part021SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part022SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part023SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)
    + (∑ q ∈ TailChunk000Sub000Block026Part024SupportExplicit,
        surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X0 q)

def surrogateDiagTailX0RatChunk000Sub000Block026Tail : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block026Part020
    + surrogateDiagTailX0RatChunk000Sub000Block026Part021
    + surrogateDiagTailX0RatChunk000Sub000Block026Part022
    + surrogateDiagTailX0RatChunk000Sub000Block026Part023
    + surrogateDiagTailX0RatChunk000Sub000Block026Part024

def surrogateDiagonalTailChunk000Sub000Block026Sum (X0 : ℕ) : ℚ :=
  surrogateDiagonalTailChunk000Sub000Block026HeadSum X0
    + surrogateDiagonalTailChunk000Sub000Block026MidSum X0
    + surrogateDiagonalTailChunk000Sub000Block026TailSum X0

def surrogateDiagTailX0RatChunk000Sub000Block026 : ℚ :=
  surrogateDiagTailX0RatChunk000Sub000Block026Part000
    + surrogateDiagTailX0RatChunk000Sub000Block026Part001
    + surrogateDiagTailX0RatChunk000Sub000Block026Part002
    + surrogateDiagTailX0RatChunk000Sub000Block026Part003
    + surrogateDiagTailX0RatChunk000Sub000Block026Part004
    + surrogateDiagTailX0RatChunk000Sub000Block026Part005
    + surrogateDiagTailX0RatChunk000Sub000Block026Part006
    + surrogateDiagTailX0RatChunk000Sub000Block026Part007
    + surrogateDiagTailX0RatChunk000Sub000Block026Part008
    + surrogateDiagTailX0RatChunk000Sub000Block026Part009
    + surrogateDiagTailX0RatChunk000Sub000Block026Part010
    + surrogateDiagTailX0RatChunk000Sub000Block026Part011
    + surrogateDiagTailX0RatChunk000Sub000Block026Part012
    + surrogateDiagTailX0RatChunk000Sub000Block026Part013
    + surrogateDiagTailX0RatChunk000Sub000Block026Part014
    + surrogateDiagTailX0RatChunk000Sub000Block026Part015
    + surrogateDiagTailX0RatChunk000Sub000Block026Part016
    + surrogateDiagTailX0RatChunk000Sub000Block026Part017
    + surrogateDiagTailX0RatChunk000Sub000Block026Part018
    + surrogateDiagTailX0RatChunk000Sub000Block026Part019
    + surrogateDiagTailX0RatChunk000Sub000Block026Part020
    + surrogateDiagTailX0RatChunk000Sub000Block026Part021
    + surrogateDiagTailX0RatChunk000Sub000Block026Part022
    + surrogateDiagTailX0RatChunk000Sub000Block026Part023
    + surrogateDiagTailX0RatChunk000Sub000Block026Part024

theorem surrogateDiagTailX0RatChunk000Sub000Block026_eq_head_add_mid_add_tail :
    surrogateDiagTailX0RatChunk000Sub000Block026Head + surrogateDiagTailX0RatChunk000Sub000Block026Mid + surrogateDiagTailX0RatChunk000Sub000Block026Tail =
      surrogateDiagTailX0RatChunk000Sub000Block026 := by
  unfold surrogateDiagTailX0RatChunk000Sub000Block026Head surrogateDiagTailX0RatChunk000Sub000Block026Mid surrogateDiagTailX0RatChunk000Sub000Block026Tail surrogateDiagTailX0RatChunk000Sub000Block026
  ring

def SurrogateDiagonalTailChunk000Sub000Block026HeadCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block026HeadSum X0 = surrogateDiagTailX0RatChunk000Sub000Block026Head

def SurrogateDiagonalTailChunk000Sub000Block026MidCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block026MidSum X0 = surrogateDiagTailX0RatChunk000Sub000Block026Mid

def SurrogateDiagonalTailChunk000Sub000Block026TailCertificateAt (X0 : ℕ) : Prop :=
  surrogateDiagonalTailChunk000Sub000Block026TailSum X0 = surrogateDiagTailX0RatChunk000Sub000Block026Tail

theorem surrogateDiagonalTailChunk000Sub000Block026_eq_cert_explicit
    (hHead : SurrogateDiagonalTailChunk000Sub000Block026HeadCertificateAt X0)
    (hMid : SurrogateDiagonalTailChunk000Sub000Block026MidCertificateAt X0)
    (hTail : SurrogateDiagonalTailChunk000Sub000Block026TailCertificateAt X0) :
    surrogateDiagonalTailChunk000Sub000Block026Sum X0 = surrogateDiagTailX0RatChunk000Sub000Block026 := by
  unfold SurrogateDiagonalTailChunk000Sub000Block026HeadCertificateAt at hHead
  unfold SurrogateDiagonalTailChunk000Sub000Block026MidCertificateAt at hMid
  unfold SurrogateDiagonalTailChunk000Sub000Block026TailCertificateAt at hTail
  unfold surrogateDiagonalTailChunk000Sub000Block026Sum
  rw [hHead, hMid, hTail]
  exact surrogateDiagTailX0RatChunk000Sub000Block026_eq_head_add_mid_add_tail

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
